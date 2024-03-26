from itertools import chain
from typing import Any, FrozenSet, List, Optional, Set, Tuple, Dict
from abc import ABC, abstractmethod


import pysmt
import unified_planning as up

from unified_planning.plans import SequentialPlan, TimeTriggeredPlan
from unified_planning.model import DurativeAction, FNode, Fluent, Action, Timing, InstantaneousAction, StartTiming, GlobalEndTiming, Effect
from unified_planning.model.fluent import get_all_fluent_exp
from tempest.converter import SMTConverter
from tempest.encoders.symbol_encoder import SymbolEncoder

# An Event is a tuple made of:
#   The action of the mutex (Action), if None is a TIL
#   The Timing in the Action/Problem
#   The FrozenSet of conditions
#   The FrozenSet of effects
Event = Tuple[Optional[Action], Timing, FrozenSet[FNode], FrozenSet[Effect]]


class BaseEncoder(ABC):
    def __init__(self, problem, pysmt_env=None):
        self.problem = problem
        self.em = self.problem.environment.expression_manager
        self.pysmt_env = pysmt_env if pysmt_env else pysmt.shortcuts.get_env()
        self.mgr = self.pysmt_env.formula_manager
        self.converters = {}

        self.objects = {}
        self.map_back_objects = {}
        i = 0
        for ut in problem.user_types:
            for obj in problem.objects(ut):
                self.objects[obj] = i
                self.map_back_objects[i] = obj
                i += 1

        self.static_fluents = problem.get_static_fluents()

        self.symenc = SymbolEncoder(self.objects, self.pysmt_env)

        self.touchers = {}
        for a in self.problem.actions:
            if isinstance(a, InstantaneousAction):
                for e in a.effects:
                    self.touchers.setdefault(e.fluent.fluent(), []).append((a, None, e))
            elif isinstance(a, DurativeAction):
                for t, le in a.effects.items():
                    for e in le:
                        self.touchers.setdefault(e.fluent.fluent(), []).append(
                            (a, t, e)
                        )
        for t, le in self.problem.timed_effects.items():
            for e in le:
                self.touchers.setdefault(e.fluent.fluent(), []).append((None, t, e))

        self._mutex_couples: Set[FrozenSet[Event]] = self._get_mutex_couples()

    def converter(self, i, w, scope):
        key = (None, i, w) if scope is None else (scope.name, i, w)
        try:
            return self.converters[key]
        except KeyError:
            c = SMTConverter(
                i=i,
                w=w,
                symenc=self.symenc,
                pysmt_env=self.pysmt_env,
                problem=self.problem,
                objects=self.objects,
                static_fluents=self.static_fluents,
                scope=scope,
            )
            self.converters[key] = c
            return c

    def to_smt(self, phi, i, w=None, scope=None):
        if w is None:
            w = i
        return self.converter(i, w, scope).to_smt(phi)

    def t(self, i):
        if i == 0:
            return self.mgr.Real(0)
        return self.symenc.t(i)

    def t_last(self):
        return self.symenc.t_last()

    def a(self, action, i):
        return self.symenc.action(action, i)

    def param(self, action, parameter, i):
        return self.symenc.parameter(action, parameter, i)

    def dur(self, action, i):
        return self.symenc.duration(action, i)

    def encode_tp(self, action, t, i):
        smt_t = self.t(i)
        smt_dur = self.dur(action, i)
        if t.is_from_start():
            if t.delay != 0:
                tp = self.mgr.Plus(smt_t, self.mgr.Real(t.delay))
            else:
                tp = smt_t
        else:
            if t.delay != 0:
                tp = self.mgr.Plus(smt_t, smt_dur, self.mgr.Real(t.delay))
            else:
                tp = self.mgr.Plus(smt_t, smt_dur)
        return tp

    def encode_problem_tp(self, t, h=None):
        if t.is_from_start():
            return self.mgr.Real(t.delay)
        else:
            assert t.delay == 0
            return self.t_last() if h is None else self.t(h - 1)

    def encode_effect(self, action, e, i, w):
        # The fluent is assigned in the current state (i)
        smt_f = self.to_smt(e.fluent, i, w, scope=action)
        # The value expression is evaluated in the previous state (i-1)
        smt_v = self.to_smt(e.value, i - 1, w, scope=action)
        # The condition is evaluated in the previous state
        smt_c = self.to_smt(e.condition, i - 1, w, scope=action)

        if e.is_assignment():
            pass
        elif e.is_increase():
            smt_v = self.mgr.Plus(self.to_smt(e.fluent, i - 1, w, scope=action), smt_v)
        elif e.is_decrease():
            smt_v = self.mgr.Minus(self.to_smt(e.fluent, i - 1, w, scope=action), smt_v)
        else:
            raise NotImplementedError

        return self.mgr.Implies(smt_c, self.mgr.EqualsOrIff(smt_f, smt_v))

    def encode_effects(self, action, t, le, i, w):
        if action is None:
            assert t.is_from_start()
            smt_tp = self.encode_problem_tp(t)
        else:
            smt_tp = self.encode_tp(action, t, w)
        eff = [self.mgr.Equals(self.t(i), smt_tp)]
        for e in le:
            eff.append(self.encode_effect(action, e, i, w))
        return self.mgr.And(eff)

    def encode_condition_or_goal(self, action, it, c, i, w, h=None):
        if action is None:
            smt_tp_1 = self.encode_problem_tp(it.lower, h)
            smt_tp_2 = self.encode_problem_tp(it.upper, h)
        else:
            smt_tp_1 = self.encode_tp(action, it.lower, w)
            smt_tp_2 = self.encode_tp(action, it.upper, w)
        if it.lower == it.upper:
            smt_tp = smt_tp_1
            cond = self.mgr.And(self.mgr.LT(self.t(i - 1), smt_tp), self.mgr.GE(self.t(i), smt_tp))
            formula = self.mgr.Implies(cond, self.to_smt(c, i - 1, w, scope=action))
        elif it.is_left_open():  # open and left open are the same
            cond_1 = self.mgr.And(self.mgr.LE(self.t(i - 1), smt_tp_1), self.mgr.GT(self.t(i), smt_tp_1))
            formula_1 = self.mgr.Implies(cond_1, self.to_smt(c, i - 1, w, scope=action))
            cond_2 = self.mgr.And(self.mgr.LT(self.t(i), smt_tp_2), self.mgr.GT(self.t(i), smt_tp_1))
            formula_2 = self.mgr.Implies(cond_2, self.to_smt(c, i, w, scope=action))
            formula = self.mgr.And(formula_1, formula_2)
        else:  # closed and right open are the same
            cond_1 = self.mgr.And(self.mgr.LT(self.t(i - 1), smt_tp_1), self.mgr.GE(self.t(i), smt_tp_1))
            formula_1 = self.mgr.Implies(cond_1, self.to_smt(c, i - 1, w, scope=action))
            cond_2 = self.mgr.And(self.mgr.LT(self.t(i), smt_tp_2), self.mgr.GE(self.t(i), smt_tp_1))
            formula_2 = self.mgr.Implies(cond_2, self.to_smt(c, i, w, scope=action))
            formula = self.mgr.And(formula_1, formula_2)
        return formula

    def encode_action_duration(self, action, i):
        smt_dur = self.dur(action, i)
        duration = action.duration
        smt_lower = self.to_smt(duration.lower, i - 1, i, scope=action)
        smt_upper = self.to_smt(duration.upper, i - 1, i, scope=action)
        l = []
        if duration.is_left_open():
            l.append(self.mgr.GT(smt_dur, smt_lower))
        else:
            l.append(self.mgr.GE(smt_dur, smt_lower))
        if duration.is_right_open():
            l.append(self.mgr.LT(smt_dur, smt_upper))
        else:
            l.append(self.mgr.LE(smt_dur, smt_upper))
        return self.mgr.And(l)

    def encode_instantaneous_action(self, action, i):
        l = []
        smt_a = self.a(action, i)

        # Encode preconditions
        for p in action.preconditions:
            l.append(self.to_smt(p, i - 1, i, scope=action))

        # Encode effects
        for e in action.effects:
            l.append(self.encode_effect(action, e, i, i))

        return self.mgr.Implies(smt_a, self.mgr.And(l))

    def encode_frame_axiom(self, i):
        res = []
        for f in self.problem.fluents:
            if f in self.static_fluents:
                continue
            for f_exp in get_all_fluent_exp(self.problem, f):
                smt_f0 = self.symenc.fluent(f_exp.fluent(), f_exp.args, i - 1)
                smt_f1 = self.symenc.fluent(f_exp.fluent(), f_exp.args, i)
                eq = self.mgr.EqualsOrIff(smt_f0, smt_f1)
                cond = self.mgr.Not(
                    eq
                )  # The fluent changes its value between step i-1 and i
                disjunctions = []  # List of possible events that can change the value
                for a, t, e in self.touchers.get(f, []):
                    if a is None:  # Timed effect
                        conj = [self.mgr.Equals(self.t(i), self.encode_problem_tp(t))]
                        conj.append(self.to_smt(e.condition, i-1))
                        trivially_false = False
                        for z, p in enumerate(e.fluent.args):
                            p = self.to_smt(p, i, scope=a)
                            va = self.to_smt(f_exp.arg(z), 0)
                            if p.is_constant() and va.is_constant():
                                if p != va:
                                    trivially_false = True
                                    break
                                # Do not add trivially true conjuncts
                            else:
                                conj.append(self.mgr.Equals(p, va))
                        if not trivially_false:
                            disjunctions.append(self.mgr.And(conj))
                    elif t is None or (
                        t.is_from_start() and t.delay == 0
                    ):  # Effect at start
                        conj = [self.a(a, i)]
                        conj.append(self.to_smt(e.condition, i-1, i, scope=a))
                        trivially_false = False
                        for z, p in enumerate(e.fluent.args):
                            p = self.to_smt(p, i, scope=a)
                            va = self.to_smt(f_exp.arg(z), 0, scope=a)
                            if p.is_constant() and va.is_constant():
                                if p != va:
                                    trivially_false = True
                                    break
                                # Do not add trivially true conjuncts
                            else:
                                conj.append(self.mgr.Equals(p, va))
                        if not trivially_false:
                            disjunctions.append(self.mgr.And(conj))
                    else:
                        for w in range(1, i + 1):
                            conj = [self.a(a, w)]
                            conj.append(self.to_smt(e.condition, i-1, w, scope=a))
                            conj.append(
                                self.mgr.Equals(self.t(i), self.encode_tp(a, t, w))
                            )
                            trivially_false = False
                            for z, p in enumerate(e.fluent.args):
                                p = self.to_smt(p, w, scope=a)
                                va = self.to_smt(f_exp.arg(z), 0, scope=a)
                                if p.is_constant() and va.is_constant():
                                    if p != va:
                                        trivially_false = True
                                        break
                                    # Do not add trivially true conjuncts
                                else:
                                    conj.append(self.mgr.Equals(p, va))
                            if not trivially_false:
                                disjunctions.append(self.mgr.And(conj))
                if len(disjunctions) == 0:  # No events => no changes
                    res.append(eq)
                elif len(disjunctions) == 1:
                    res.append(self.mgr.Implies(cond, disjunctions[0]))
                else:
                    res.append(self.mgr.Implies(cond, self.mgr.Or(disjunctions)))
                    for x in range(len(disjunctions)):  # Only one is possible
                        for y in range(x + 1, len(disjunctions)):
                            res.append(
                                self.mgr.Not(
                                    self.mgr.And(disjunctions[x], disjunctions[y])
                                )
                            )
        return self.mgr.And(res)

    def is_mutex(self, a_precond, a_effects, b_precond, b_effects):
        fve = self.problem.environment.free_vars_extractor

        a_p = set(x.fluent() for p in a_precond for x in fve.get(p))
        b_p = set(x.fluent() for p in b_precond for x in fve.get(p))

        def get_red_fluents(effect):
            for x in chain(*map(fve.get, (effect.condition, effect.fluent, effect.value))):
                yield x.fluent()

        a_e = set()
        for e in a_effects:
            a_e.add(e.fluent.fluent())
            a_p.update(get_red_fluents(e))

        b_e = set()
        for e in b_effects:
            b_e.add(e.fluent.fluent())
            b_p.update(get_red_fluents(e))

        return not (a_p.isdisjoint(b_e) and b_p.isdisjoint(a_e) and a_e.isdisjoint(b_e))

    def encode_non_self_overlapping(self, i):
        res = []
        for act in self.problem.actions:
            if not isinstance(act, DurativeAction):
                continue
            a_i = self.a(act, i)
            a_i_params = tuple(self.param(act, p, i) for p in act.parameters)
            for j in range(1, i):
                a_j = self.a(act, j)
                a_j_params = tuple(self.param(act, p, j) for p in act.parameters)
                assert len(a_i_params) == len(a_j_params)

                same_parameters = self.mgr.And((self.mgr.EqualsOrIff(a_i_p, a_j_p) for a_i_p, a_j_p in zip(a_i_params, a_j_params)))
                actions_and_same_parameters = self.mgr.And(a_i, a_j, same_parameters)

                end_a_j = self.mgr.Plus(self.t(j), self.dur(act, j))
                start_a_i = self.t(i)
                end_a_j_before_start_a_i = self.mgr.LE(end_a_j, start_a_i)

                res.append(self.mgr.Implies(actions_and_same_parameters, end_a_j_before_start_a_i))
        return self.mgr.And(res)

    def initial_state(self):
        res = []
        for f, v in self.problem.initial_values.items():
            smt_f = self.to_smt(f, 0)
            smt_v = self.to_smt(v, 0)
            res.append(self.mgr.EqualsOrIff(smt_f, smt_v))
        for c in self.symenc.type_constraints[0]:
            res.append(c)
        return self.mgr.And(res)

    def extract_plan(self, model, h):
        res = []
        for i in range(h):
            t = model.get_py_value(self.t(i))
            for a in self.problem.actions:
                if model.get_py_value(self.a(a, i)):
                    d = (
                        model.get_py_value(self.dur(a, i))
                        if isinstance(a, up.model.DurativeAction)
                        else None
                    )
                    params = []
                    for p in a.parameters:
                        pv = model.get_py_value(self.symenc.parameter(a, p, i))
                        if p.type.is_user_type():
                            assert pv.denominator == 1
                            pv = self.map_back_objects[pv.numerator]
                        elif p.type.is_int_type():
                            assert pv.denominator == 1
                            pv = pv.numerator
                        params.append(pv)
                    res.append((t, a(*params), d))
        if self.problem.kind.has_continuous_time():
            return TimeTriggeredPlan(res)
        else:
            return SequentialPlan([ai for _, ai, _ in res])

    @abstractmethod
    def encode_step_zero(self) -> Optional[Any]:
        pass

    @abstractmethod
    def encode_step(self, step: int) -> Tuple[Any, Any]:
        pass


    #TODO remove
    # def _create_fluents_modification_map(self) -> Dict[Fluent, Dict[FNode, Set[Tuple[Optional[Action], Timing, bool, Optional[int]]]]]:
    #     # Create a map from a fluent to the event time that modifies that fluent
    #     # The values in the map represent:
    #     #   the action that contains the event (if None -> TILS or goal)
    #     #   the relative time (absolute if the action is None)
    #     #   True if the value is written by this event, False if it's red
    #     #   the ID of TILS, to prevent a til from being conflicting with itself
    #     # The returned map is a map from a lifted fluent to the mapping above (for efficiency)
    #     fluents_modification_map: Dict[Fluent, Dict[FNode, Set[Tuple[Optional[Action], Timing, bool, Optional[int]]]]] = {}

    #     # definition of macro to simplify the code
    #     fve = self.problem.environment.free_vars_extractor
    #     tils_id: List[int] = [0] # workaround to modify the out-of-scope counter in the "add_to_map" macro
    #     def add_to_map(fluent_exp, action, timing, is_write):
    #         til_id = None
    #         if action is None:
    #             til_id = tils_id[0]
    #             tils_id[0] = til_id + 1
    #         fluent = fluent_exp.fluent()
    #         modifications_map: Dict[FNode, Set[Tuple[Optional[Action], Timing, bool]]] = fluents_modification_map.setdefault(fluent, {})
    #         modifications_map.setdefault(fluent_exp, set()).add((action, timing, is_write, til_id))

    #     def add_expression_to_map(expression, action, timing):
    #         for x in fve.get(expression):
    #             add_to_map(x, action, timing, False)

    #     def add_effect_to_map(effect, action, timing):
    #         for x in effect.fluent.args:
    #             add_expression_to_map(x, action, timing)
    #         add_expression_to_map(effect.value, action, timing)
    #         add_expression_to_map(effect.condition, action, timing)
    #         add_to_map(effect.fluent, action, timing, True)

    #     start_timing = StartTiming()
    #     global_end_timing = GlobalEndTiming()

    #     for act in self.problem.actions:
    #         if isinstance(act, InstantaneousAction):
    #             for p in act.preconditions:
    #                 add_expression_to_map(p, act, start_timing)
    #             for eff in act.effects:
    #                 add_effect_to_map(eff, act, start_timing)
    #         else:
    #             assert isinstance(act, DurativeAction)
    #             for interval, cl in act.conditions.items():
    #                 for c in cl:
    #                     if not interval.is_left_open():
    #                         add_expression_to_map(c, act, interval.lower)
    #                     if not interval.is_right_open():
    #                         add_expression_to_map(c, act, interval.upper)

    #             for timing, el in act.effects.items():
    #                 for eff in el:
    #                     add_effect_to_map(eff, act, timing)

    #     for interval, cl in self.problem.timed_goals.items():
    #         for c in cl:
    #             if not interval.is_left_open():
    #                 add_expression_to_map(c, None, interval.lower)
    #             if not interval.is_right_open():
    #                 add_expression_to_map(c, None, interval.upper)

    #     for timing, el in self.problem.timed_effects.items():
    #         for eff in el:
    #             add_effect_to_map(eff, None, timing)

    #     for g in self.problem.goals:
    #         add_expression_to_map(g, None, global_end_timing)

    #     return fluents_modification_map

    # def _get_mutex_couples(self) -> List[Tuple[Event, Event]]:
    #     mutex_couples: List[Tuple[Event, Event]] = []
    #     fluents_modification_map = self._create_fluents_modification_map()
    #     for fluent, modifications_map in fluents_modification_map.items():
    #         for fluent_exp_a, modifications_set_a in modifications_map.items():
    #             for action_a, timing_a, is_write_a, til_id_a in modifications_set_a:
    #                 for fluent_exp_b, modifications_set_b in modifications_map.items():
    #                     for action_b, timing_b, is_write_b, til_id_b in modifications_set_b:
    #                         if (not is_write_a and not is_write_b) or (til_id_a is not None and til_id_a == til_id_b):
    #                             continue
    #                         a_tup = (fluent_exp_a, action_a, timing_a, is_write_a, til_id_a)
    #                         b_tup = (fluent_exp_b, action_b, timing_b, is_write_b, til_id_b)
    #                         mutex_couples.append((a_tup, b_tup))

    #     return mutex_couples

    def _get_events(self) -> Set[Event]:
        events: Set[Event] = set()
        start_timing = StartTiming()
        global_end_timing = GlobalEndTiming()

        for act in self.problem.actions:
            if isinstance(act, InstantaneousAction):
                events.add((act, start_timing, frozenset(act.preconditions), frozenset(act.effects)))
            else:
                assert isinstance(act, DurativeAction)
                for interval, cl in act.conditions.items():
                    conds = frozenset(cl)
                    effs = frozenset()
                    if not interval.is_left_open():
                        events.add((act, interval.lower, conds, effs))
                    if not interval.is_right_open():
                        events.add((act, interval.upper, conds, effs))

                for timing, el in act.effects.items():
                    events.add((act, timing, frozenset(), frozenset(el)))

        for interval, cl in self.problem.timed_goals.items():
            conds = frozenset(cl)
            effs = frozenset()
            if not interval.is_left_open():
                events.add((None, interval.lower, conds, effs))
            if not interval.is_right_open():
                events.add((None, interval.upper, conds, effs))

        for timing, el in self.problem.timed_effects.items():
            events.add((None, timing, frozenset(), frozenset(el)))

        events.add((None, global_end_timing, frozenset(self.problem.goals), frozenset()))

        return events

    def _get_conditions(self, action, timing):
        conditions = set()
        def add_durative_conditions(conds):
            for interval, gl in conds.items():
                if not interval.is_left_open() and interval.lower == timing:
                    conditions.update(gl)
                if not interval.is_right_open() and interval.upper == timing:
                    conditions.update(gl)

        if action is None:
            # assert timing.is_global()
            if timing.is_from_end():
                conditions.update(self.problem.goals)
            add_durative_conditions(self.problem.timed_goals)
        elif isinstance(action, InstantaneousAction):
            assert timing.is_from_start() and not timing.is_global()
            conditions.update(action.preconditions)
        elif isinstance(action, DurativeAction):
            add_durative_conditions(action.conditions)

        return conditions

    def _get_effects(self, action, timing):
        effects = set()

        if action is None:
            # assert timing.is_global() and timing.is_from_start()
            effects.update(self.problem.timed_effects.get(timing, tuple()))
        elif isinstance(action, InstantaneousAction):
            assert timing.is_from_start() and not timing.is_global()
            effects.update(action.effects)
        elif isinstance(action, DurativeAction):
            effects.update(action.effects.get(timing, tuple()))

        return effects

    def _get_mutex_couples(self) -> Set[FrozenSet[Event]]:
        mutex_couples: Set[FrozenSet[Event]] = set()
        events = list(self._get_events())
        for i, event_a in enumerate(events):
            action_a, timing_a, cond_a, eff_a = event_a
            for event_b in events[i+1:]:
                action_b, timing_b, cond_b, eff_b = event_b
                if action_a == action_b and (action_a is None or timing_a == timing_b):
                    continue
                if self.is_mutex(cond_a, eff_a, cond_b, eff_b):
                    mutex_couples.add(frozenset(((action_a, timing_a), (action_b, timing_b))))
        return mutex_couples

    def encode_mutex_constraints(self, i, j, h):
        res = []
        def encode_timing(action, timing, step):
            if isinstance(action, InstantaneousAction):
                assert timing.is_from_start() and not timing.is_global()
                return self.t(step)
            elif isinstance(action, DurativeAction):
                assert not timing.is_global()
                return self.encode_tp(action, timing, step)
            else:
                # assert action is None and timing.is_global() -> It is commented due to a problem in the UnifiedPlanning test-cases, where some tils have StartTiming instead of GlobalStartTiming
                return self.encode_problem_tp(timing, h)

        for (action_a, timing_a), (action_b, timing_b) in self._mutex_couples:
            if i == j and action_a == action_b:
                continue
            time_of_a = encode_timing(action_a, timing_a, i)
            time_of_b = encode_timing(action_b, timing_b, j)
            same_timing = self.mgr.Equals(time_of_a, time_of_b)

            if action_a is None:
                assert action_b is not None
                # a is a tils, b is an action
                b_j = self.a(action_b, j)
                res.append(self.mgr.Not(self.mgr.And(b_j, same_timing)))
            else:
                a_i = self.a(action_a, i)
                if action_b is None:
                    # a is an action, b is a tils
                    res.append(self.mgr.Not(self.mgr.And(a_i, same_timing)))
                else:
                    # both are actions
                    b_j = self.a(action_b, j)
                    res.append(self.mgr.Not(self.mgr.And(a_i, b_j, same_timing)))

        return self.mgr.And(res)

    def encode_increasing_time(self, i):
        if self.problem.epsilon is None:
            return self.mgr.LT(self.t(i - 1), self.t(i))
        assert self.problem.epsilon > 0
        return self.mgr.LE(self.mgr.Plus(self.t(i - 1), self.mgr.Real(self.problem.epsilon)), self.t(i))
