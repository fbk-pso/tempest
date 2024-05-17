from fractions import Fraction
from itertools import chain, product
from typing import Any, Dict, FrozenSet, Iterable, List, Optional, Set, Tuple, Union
from functools import lru_cache
from abc import ABC, abstractmethod
import warnings
import pysmt

import unified_planning as up
from unified_planning.engines import CompilationKind
from unified_planning.exceptions import UPNoSuitableEngineAvailableException
from unified_planning.model import DurativeAction, FNode, Action, Timing, InstantaneousAction, StartTiming, GlobalEndTiming, Effect, Problem, Parameter, TimeInterval, Fluent
from unified_planning.model.fluent import get_all_fluent_exp
from unified_planning.model.types import domain_size, domain_item
from unified_planning.model.walkers import Simplifier, AnyGetter
from unified_planning.plans import SequentialPlan, TimeTriggeredPlan

from tempest.converter import SMTConverter
from tempest.encoders.symbol_encoder import SymbolEncoder

# An Event is a tuple made of:
#   The action of the mutex (Action), if None is a TIL
#   The Timing in the Action/Problem
#   The FrozenSet of conditions
#   The FrozenSet of effects
Event = Tuple[Optional[Action], Timing, FrozenSet[FNode], FrozenSet[Effect]]

# A Toucher is a tuple made of:
#   The action containing the effect (None if it is a timed effect)
#   The timing of the effect in the action (None if it is an InstantaneousAction)
#   The Effect "touching" the correct fluent (the modified fluent)
Toucher = Tuple[Optional[Action], Optional[Timing], Effect]


class BaseEncoder(ABC):
    def __init__(self, problem: Problem, pysmt_env: pysmt.environment.Environment, epsilon: Optional[Fraction] = None, optimal: bool = False,
                 ground_abstract_step: bool = True, grounder_name: Optional[str] = None):
        self.problem = problem
        self.epsilon = epsilon
        self.simplifier = Simplifier(problem.environment, problem)
        self.param_getter = AnyGetter(lambda x: x.is_parameter_exp())
        self.em = self.problem.environment.expression_manager
        self.pysmt_env = pysmt_env
        self.mgr = self.pysmt_env.formula_manager
        self.optimal = optimal
        self.ground_abstract_step = ground_abstract_step
        grounded_problem = problem
        self.map_back_action_instance = lambda x: x
        if ground_abstract_step and optimal:
            try:
                with self.problem.environment.factory.Compiler(name=grounder_name, compilation_kind=CompilationKind.GROUNDING, problem_kind=problem.kind) as grounder:
                    comp_res = grounder.compile(problem, CompilationKind.GROUNDING)
                    grounded_problem = comp_res.problem
                    self.map_back_action_instance = comp_res.map_back_action_instance
            except UPNoSuitableEngineAvailableException:
                warnings.warn("There are no grounders for this problem so the ground_abstract_step is disabled in this solve call", UserWarning)
                self.ground_abstract_step = False

        self.abstract_step_actions = grounded_problem.actions
        self.abstract_step_metrics = grounded_problem.quality_metrics
        self.fluent_mod_formulae_mapping: Dict[Any, Any] = {}

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

        self.touchers: Dict[Fluent, Dict[FNode, List[Toucher]]] = self._get_touchers(problem)
        self.abstract_step_touchers: Dict[Fluent, Dict[FNode, List[Toucher]]] = self.touchers
        if ground_abstract_step:
            self.abstract_step_touchers = self._get_touchers(grounded_problem)

        self._mutex_couples: Set[FrozenSet[Event]] = self._get_mutex_couples()

    def converter(self, i: int, w: Optional[int], scope: Optional[Action]):
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

    def to_smt(self, phi: FNode, i: int, w: Optional[int]=None, scope: Optional[Action]=None):
        if w is None:
            w = i
        return self.converter(i, w, scope).to_smt(phi)

    def t(self, i: int):
        if i == 0:
            return self.mgr.Real(-1)
        return self.symenc.t(i)

    def t_a(self, a: Action, h: int):
        return self.symenc.t_a(a, h)

    def t_last(self):
        return self.symenc.t_last()

    def a(self, action: Action, i: int):
        return self.symenc.action(action, i)

    def param(self, action: Action, parameter: Parameter, i):
        return self.symenc.parameter(action, parameter, i)

    def dur(self, action: Action, i: int):
        return self.symenc.duration(action, i)

    def encode_tp(self, action: Action, t: Timing, i: int, h: Optional[int]):
        smt_t = self.t(i) if h is None or i < h else self.t_a(action, h)
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

    def encode_problem_tp(self, t: Timing, h: int):
        if t.is_from_start():
            return self.mgr.Real(t.delay)
        else:
            assert t.delay == 0
            return self.t_last() if h is None else self.t(h - 1)

    def encode_effect(self, action: Optional[Action], e: Effect, i: int, w: int):
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

    def encode_effects(self, action: Optional[Action], t: Timing, le: Iterable[Effect], i: int, w: Optional[int], h: int):
        if action is None:
            assert t.is_from_start()
            smt_tp = self.encode_problem_tp(t, None)
        else:
            smt_tp = self.encode_tp(action, t, w, h)
        eff = [self.mgr.Equals(self.t(i), smt_tp)]
        for e in le:
            eff.append(self.encode_effect(action, e, i, w))
        effect_formula = self.mgr.And(eff)
        if self.optimal:
            effect_in_abstract_step = self.mgr.LT(self.t(h-1), smt_tp)
            effect_formula = self.mgr.Or(effect_formula, effect_in_abstract_step)
        return effect_formula

    def encode_condition_or_goal(self, action: Optional[Action], it: TimeInterval, c: FNode, i: int, w: Optional[int], h: int):
        if action is None:
            smt_tp_1 = self.encode_problem_tp(it.lower, h)
            smt_tp_2 = self.encode_problem_tp(it.upper, h)
        else:
            smt_tp_1 = self.encode_tp(action, it.lower, w, h)
            smt_tp_2 = self.encode_tp(action, it.upper, w, h)

        non_empty_interval_operand = self.mgr.GE
        if it.is_left_open() or it.is_right_open():
            non_empty_interval_operand = self.mgr.GT
        if self._is_never_empty_interval(it):
            # adding True instead of a trivially True expression (e.g. 5 > 3)
            non_empty_interval_operand = lambda x, y: self.mgr.TRUE()

        if self._is_always_empty_interval(it):
            return self.mgr.TRUE()
        elif it.lower == it.upper:
            smt_tp = smt_tp_1
            cond = self.mgr.And(self.mgr.LT(self.t(i - 1), smt_tp), self.mgr.GE(self.t(i), smt_tp))
            formula = self.mgr.Implies(cond, self.to_smt(c, i - 1, w, scope=action))
        elif it.is_left_open():  # open and left open are the same
            cond_1 = self.mgr.And(self.mgr.LE(self.t(i - 1), smt_tp_1), self.mgr.GT(self.t(i), smt_tp_1), non_empty_interval_operand(smt_tp_2, smt_tp_1))
            formula_1 = self.mgr.Implies(cond_1, self.to_smt(c, i - 1, w, scope=action))
            cond_2 = self.mgr.And(self.mgr.LT(self.t(i), smt_tp_2), self.mgr.GT(self.t(i), smt_tp_1))
            formula_2 = self.mgr.Implies(cond_2, self.to_smt(c, i, w, scope=action))
            formula = self.mgr.And(formula_1, formula_2)
        else:  # closed and right open are the same
            cond_1 = self.mgr.And(self.mgr.LT(self.t(i - 1), smt_tp_1), self.mgr.GE(self.t(i), smt_tp_1), non_empty_interval_operand(smt_tp_2, smt_tp_1))
            formula_1 = self.mgr.Implies(cond_1, self.to_smt(c, i - 1, w, scope=action))
            cond_2 = self.mgr.And(self.mgr.LT(self.t(i), smt_tp_2), self.mgr.GE(self.t(i), smt_tp_1))
            formula_2 = self.mgr.Implies(cond_2, self.to_smt(c, i, w, scope=action))
            formula = self.mgr.And(formula_1, formula_2)

        if self.optimal:
            last_concrete_step_time = self.t(h-1)
            if last_concrete_step_time != smt_tp_1:

                start_condition_after_last_concrete_step = self.mgr.LT(last_concrete_step_time, smt_tp_1)

                p = self._get_sorted_parameters(c, action)
                if w != h or not p:
                    condition_last_concrete_step = self.to_smt(c, h-1, w, action)
                else:
                    condition_last_concrete_step_clauses = []
                    for p_ass in self._get_possible_parameters_assignments(p):
                        subs = dict(zip(p, p_ass))
                        condition_last_concrete_step_clauses.append(self.to_smt(c.substitute(subs), h-1))
                    condition_last_concrete_step = self.mgr.Or(condition_last_concrete_step_clauses)

                condition_abstract_step = self.mgr.Or((self.fluent_mod(exp, action, w,h) for exp in self._get_sorted_fve(c)))

                extra_formula = self.mgr.Implies(start_condition_after_last_concrete_step, self.mgr.Or(condition_last_concrete_step, condition_abstract_step))
                formula = self.mgr.And(formula, extra_formula)

        return formula

    def _is_always_empty_interval(self, interval: TimeInterval) -> bool:
        lower, upper = interval.lower, interval.upper
        if lower.is_from_start() != upper.is_from_start():
            # One is from start and the other from end
            return False
        elif interval.is_left_open() or interval.is_right_open():
            return lower.delay >= upper.delay
        else:
            return lower.delay > upper.delay

    def _is_never_empty_interval(self, interval: TimeInterval) -> bool:
        lower, upper = interval.lower, interval.upper
        if lower.is_from_start() != upper.is_from_start():
            # One is from start and the other from end
            return False
        elif interval.is_left_open() or interval.is_right_open():
            return lower.delay < upper.delay
        else:
            return lower.delay <= upper.delay

    def encode_action_duration(self, action: DurativeAction, i: int):
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

    def encode_instantaneous_action(self, action: InstantaneousAction, i: int):
        l = []
        smt_a = self.a(action, i)

        # Encode preconditions
        for p in action.preconditions:
            l.append(self.to_smt(p, i - 1, i, scope=action))
        # Encode effects
        for e in action.effects:
            l.append(self.encode_effect(action, e, i, i))

        return self.mgr.Implies(smt_a, self.mgr.And(l))

    def encode_frame_axiom(self, i: int, h: int):
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
                fluent_dict = self.touchers.get(f, {})
                for a, t, e in chain(*fluent_dict.values()):
                    if a is None:  # Timed effect
                        conj = [self.mgr.Equals(self.t(i), self.encode_problem_tp(t, h))]
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
                                self.mgr.Equals(self.t(i), self.encode_tp(a, t, w, h))
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

    def is_mutex(self, a_precond: Iterable[FNode], a_effects: Iterable[Effect], b_precond: Iterable[FNode], b_effects: Iterable[Effect]):

        a_p = set(x.fluent() for p in a_precond for x in self._get_sorted_fve(p))
        b_p = set(x.fluent() for p in b_precond for x in self._get_sorted_fve(p))

        def get_red_fluents(effect):
            for x in chain(*map(self._get_sorted_fve, (effect.condition, effect.fluent, effect.value))):
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

    def encode_non_self_overlapping(self, i: int):
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

    def extract_plan(self, model: pysmt.solvers.solver.Model, h: int) -> Union[SequentialPlan, TimeTriggeredPlan]:
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

    def _get_touchers(self, problem: Problem) -> Dict[Fluent, Dict[FNode, List[Toucher]]]:
        touchers = {}
        for a in problem.actions:
            if isinstance(a, InstantaneousAction):
                for e in a.effects:
                    fluent_dict = touchers.setdefault(e.fluent.fluent(), {})
                    fluent_dict.setdefault(e.fluent, []).append((a, None, e))
            elif isinstance(a, DurativeAction):
                for t, le in a.effects.items():
                    for e in le:
                        fluent_dict = touchers.setdefault(e.fluent.fluent(), {})
                        fluent_dict.setdefault(e.fluent, []).append((a, t, e))
        for t, le in problem.timed_effects.items():
            for e in le:
                fluent_dict = touchers.setdefault(e.fluent.fluent(), {})
                fluent_dict.setdefault(e.fluent, []).append((None, t, e))
        return touchers

    def encode_mutex_constraints(self, i: int, j: int, h: int):
        res = []
        def encode_timing(action, timing, step):
            if isinstance(action, InstantaneousAction):
                assert timing.is_from_start() and not timing.is_global()
                return self.t(step)
            elif isinstance(action, DurativeAction):
                assert not timing.is_global()
                return self.encode_tp(action, timing, step, h)
            else:
                # assert action is None and timing.is_global() -> It is commented due to a problem in the UnifiedPlanning test-cases, where some tils have StartTiming instead of GlobalStartTiming
                return self.encode_problem_tp(timing, h)

        for (action_a, timing_a), (action_b, timing_b) in self._mutex_couples:
            def is_global_end(timing):
                return timing.is_global() and timing.is_from_end()

            if (i == j and action_a == action_b) or is_global_end(timing_a) or is_global_end(timing_b):
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

    def encode_increasing_time(self, i: int):
        if i == 1:
            # First valid step must be >= 0
            return self.mgr.LE(self.mgr.Real(0), self.t(i))
        if self.epsilon is None:
            return self.mgr.LT(self.t(i - 1), self.t(i))
        assert self.epsilon > 0
        return self.mgr.LE(self.mgr.Plus(self.t(i - 1), self.mgr.Real(self.epsilon)), self.t(i))

    @lru_cache(maxsize=None)
    def _fluent_mod_formula(self, fluent: Fluent, fluent_exp: FNode, h: int):
        assert isinstance(fluent_exp, FNode)
        assert not (self.ground_abstract_step and self.param_getter.get(fluent_exp))
        res = []
        abstract_fluent_touchers = self.abstract_step_touchers.get(fluent, None)
        if abstract_fluent_touchers is None:
            return self.mgr.FALSE()

        if self.ground_abstract_step:
            assert fluent_exp is not None
            fluent_touchers_gen = abstract_fluent_touchers.get(fluent_exp, [])
        else:
            assert fluent_exp is None
            fluent_touchers_gen = chain(*abstract_fluent_touchers.values())

        for action, timing, eff in fluent_touchers_gen:
            if action is None:
                til_in_abstract_step = self.mgr.GT(self.encode_problem_tp(timing, h), self.t(h-1))
                res.append(til_in_abstract_step)
            elif timing is None:
                assert isinstance(action, InstantaneousAction)
                action_in_abstract_step = self.a(action, h)
                res.append(action_in_abstract_step)
            else:
                assert isinstance(action, DurativeAction)
                last_concrete_step_time = self.t(h-1)
                concrete_action, parameters_assignment = action, {}
                if self.ground_abstract_step:
                    concrete_ai = self.map_back_action_instance(action())
                    concrete_action = concrete_ai.action
                    parameters_assignment = dict(zip(action.parameters, concrete_ai.actual_parameters))
                    # TODO: future improvements, it would be nice to remove action parameters that do not
                    # appear in the effect from the assignment mapping
                for i in range(1, h):
                    a_i = self.a(concrete_action, i)
                    parameters_equality = []
                    for param_exp, obj_exp in parameters_assignment.items():
                        parameters_equality.append(self.mgr.EqualsOrIff(self.to_smt(param_exp, i, i, scope=concrete_action), self.to_smt(obj_exp, i)))
                    p_eq = self.mgr.And(parameters_equality)
                    effect_time = self.encode_tp(concrete_action, timing, i, h)
                    effect_in_abstract_step = self.mgr.GT(effect_time, last_concrete_step_time)
                    effect_performed_in_abstract_step = self.mgr.And(a_i, p_eq, effect_in_abstract_step)
                    res.append(effect_performed_in_abstract_step)
                # No need to check for parameters because either the action is grounded or the fluent_mod is considered on the lifted fluent
                a_h = self.a(action, h)
                res.append(a_h)

        fluent_mod_formula = self.mgr.Or(res)
        naming = fluent if fluent_exp is None else fluent_exp
        fluent_mod_var = self.mgr.FreshSymbol(template=f"phi_{h}_mod_{naming}%d")
        self.fluent_mod_formulae_mapping[fluent_mod_formula] = fluent_mod_var
        assert fluent_mod_var is not None
        return fluent_mod_var

    @lru_cache(maxsize=None)
    def fluent_mod(self, fluent_exp: FNode, a: Optional[Action], w: Optional[int], h: int):
        fluent_parameters = self._get_sorted_parameters(fluent_exp, a)
        if not self.ground_abstract_step:
            return self._fluent_mod_formula(fluent_exp.fluent(), None, h)
        elif not fluent_parameters:
            return self._fluent_mod_formula(fluent_exp.fluent(), fluent_exp, h)

        res = []
        assert a is not None and w is not None
        # relevant parameters are computed in order to eliminate randomness in the order
        # of the parameters given to the self._get_possible_parameters_assignments
        for parameters_value in self._get_possible_parameters_assignments(fluent_parameters):
            sub_res = []
            assignments = dict(zip(fluent_parameters, parameters_value))
            ground_fluent_exp = fluent_exp.substitute(assignments)
            sub_res.append(self._fluent_mod_formula(ground_fluent_exp.fluent(), ground_fluent_exp, h))
            for param_exp, obj_exp in assignments.items():
                sub_res.append(self.mgr.EqualsOrIff(self.to_smt(param_exp, w, w, scope=a), self.to_smt(obj_exp, w)))
            res.append(self.mgr.And(sub_res))
        return self.mgr.Or(res)

    @lru_cache(maxsize=None)
    def _get_possible_parameters_assignments(self, parameters: Tuple[FNode, ...]) -> Tuple[Tuple[FNode, ...], ...]:
        # Generates all the possible assignments that the given parameters have in the given problem
        types = tuple(param.type for param in parameters)
        domain_sizes = tuple(domain_size(self.problem, t) for t in types)
        items_list: List[List[FNode]] = []
        for size, type in zip(domain_sizes, types):
            items_list.append(
                [domain_item(self.problem, type, j) for j in range(size)]
            )
        return tuple(product(*items_list))

    def encode_abstract_instantaneous_action(self, action: InstantaneousAction, h: int):
        assert self.optimal
        l = []
        a_h = self.a(action, h)

        # Encode preconditions
        for p in action.preconditions:
            params = self._get_sorted_parameters(p, action)
            if not params:
                condition_last_concrete_step = self.to_smt(p, h-1, h, scope=action)
            else:
                condition_last_concrete_step_clauses = []
                for p_ass in self._get_possible_parameters_assignments(params):
                    subs = dict(zip(params, p_ass))
                    condition_last_concrete_step_clauses.append(self.to_smt(p.substitute(subs), h-1))
                condition_last_concrete_step = self.mgr.Or(condition_last_concrete_step_clauses)

            condition_abstract_step = self.mgr.Or((self.fluent_mod(exp, action, h, h) for exp in self._get_sorted_fve(p)))
            l.append(self.mgr.Or(condition_last_concrete_step, condition_abstract_step))
        return self.mgr.Implies(a_h, self.mgr.And(l))

    def phi_sched(self, h: int):
        res = []

        for interval, goals in self.problem.timed_goals.items():
            timing = interval.lower
            interval_in_abstract_step = self.mgr.GT(self.encode_problem_tp(timing, h), self.t(h-1))
            empty_interval_operand = self.mgr.LE
            if interval.is_left_open() or interval.is_right_open():
                empty_interval_operand = self.mgr.LT
            interval_not_empty = empty_interval_operand(self.encode_problem_tp(interval.lower, h), self.encode_problem_tp(interval.upper, h))
            for goal in goals:
                goal_not_satisfied = self.mgr.Not(self.to_smt(goal, h-1))
                res.append(self.mgr.Implies(
                    self.mgr.And(goal_not_satisfied, interval_in_abstract_step, interval_not_empty),
                    self._phi_sched_parametrized_formula(goal, timing, None, None, h)
                ))

        for a in filter(lambda a: isinstance(a, DurativeAction), self.problem.actions):
            for s in range(1, h):
                sub_res = []
                for interval, cl in a.conditions.items():
                    timing = interval.lower
                    interval_in_abstract_step = self.mgr.GT(self.encode_tp(a, timing, s, h), self.t(h-1))
                    empty_interval_operand = self.mgr.LE
                    if interval.is_left_open() or interval.is_right_open():
                        empty_interval_operand = self.mgr.LT
                    interval_not_empty = empty_interval_operand(self.encode_tp(a, interval.lower, s, h), self.encode_tp(a, interval.upper, s, h))
                    for cond in cl:
                        cond_not_satisfied = self.mgr.Not(self.to_smt(cond, h-1, s, scope=a))
                        sub_res.append(self.mgr.Implies(
                            self.mgr.And(cond_not_satisfied, interval_in_abstract_step, interval_not_empty),
                            self._phi_sched_parametrized_formula(cond, timing, a, s, h)
                        ))
                res.append(self.mgr.Implies(self.a(a, s), self.mgr.And(sub_res)))

        for a in self.abstract_step_actions:
            assert self.epsilon > 0
            res.append(self.mgr.LE(self.mgr.Plus(self.t(h-1), self.mgr.Real(self.epsilon)), self.t_a(a, h)))
            if isinstance(a, InstantaneousAction):
                sub_res = []
                for cond in a.preconditions:
                    cond_params = self._get_sorted_parameters(cond, a)
                    if not cond_params:
                        cond_not_satisfied = self.mgr.Not(self.to_smt(cond, h-1))
                    else:
                        cond_not_satisfied_clauses = []
                        for p_ass in self._get_possible_parameters_assignments(cond_params):
                            subs = dict(zip(cond_params, p_ass))
                            cond_not_satisfied_clauses.append(self.mgr.Not(self.to_smt(cond.substitute(subs), h-1)))
                        cond_not_satisfied = self.mgr.And(cond_not_satisfied_clauses)
                    sub_res.append(self.mgr.Implies(
                        cond_not_satisfied,
                        self._phi_sched_parametrized_formula(cond, None, a, h, h)
                    ))
            else:
                assert isinstance(a, DurativeAction)
                sub_res = []
                for interval, cl in a.conditions.items():
                    timing = interval.lower
                    empty_interval_operand = self.mgr.LE
                    if interval.is_left_open() or interval.is_right_open():
                        empty_interval_operand = self.mgr.LT
                    interval_not_empty = empty_interval_operand(self.encode_tp(a, interval.lower, h, h), self.encode_tp(a, interval.upper, h, h))
                    for cond in cl:
                        cond_params = self._get_sorted_parameters(cond, a)
                        if not cond_params:
                            cond_not_satisfied = self.mgr.Not(self.to_smt(cond, h-1))
                        else:
                            cond_not_satisfied_clauses = []
                            for p_ass in self._get_possible_parameters_assignments(cond_params):
                                subs = dict(zip(cond_params, p_ass))
                                cond_not_satisfied_clauses.append(self.mgr.Not(self.to_smt(cond.substitute(subs), h-1)))
                            cond_not_satisfied = self.mgr.And(cond_not_satisfied_clauses)
                        sub_res.append(self.mgr.Implies(
                            self.mgr.And(cond_not_satisfied, interval_not_empty),
                            self._phi_sched_parametrized_formula(cond, timing, a, h, h)
                        ))
                res.append(self.mgr.Implies(self.a(a, h), self.mgr.And(sub_res)))

        # TODO check completeness
        return self.mgr.And(res)

    def _phi_sched_parametrized_formula(self, phi: FNode, t: Optional[Timing], a: Optional[Action], w: Optional[int], h: int):
        res = []
        if a is None:
            assert w is None
            phi_time = self.encode_problem_tp(t, h)
        elif t is None:
            assert isinstance(a, InstantaneousAction) and w is not None
            phi_time = self.t_a(a, h)
        else:
            assert isinstance(a, DurativeAction) and w is not None
            phi_time = self.encode_tp(a, t, w, h)

        for fluent_exp in self._get_sorted_fve(phi):
            fluent_params = self._get_sorted_parameters(fluent_exp, a)
            if not fluent_params or not self.ground_abstract_step:
                res.append(self.mgr.And(self.fluent_mod(fluent_exp, a, w, h), self._phi_sched_formula(phi_time, fluent_exp, h)))
            else:
                assert w < h, "parameters should come only from actions started in concrete steps"
                for parameter_assignment in self._get_possible_parameters_assignments(fluent_params):
                    assignments = dict(zip(fluent_params, parameter_assignment))
                    p_eq = []
                    for param_exp, obj_exp in assignments.items():
                        p_eq.append(self.mgr.EqualsOrIff(self.to_smt(param_exp, w, w, scope=a), self.to_smt(obj_exp, w)))
                    parameters_equality = self.mgr.And(p_eq)
                    ground_fluent_exp = fluent_exp.substitute(assignments)
                    res.append(self.mgr.And(parameters_equality, self.fluent_mod(ground_fluent_exp, a, w, h), self._phi_sched_formula(phi_time, ground_fluent_exp, h)))

        return self.mgr.Or(res)

    def _phi_sched_formula(self, phi_time, fluent_exp: FNode, h: int):
        res = []
        last_t = self.t(h-1)
        if self.ground_abstract_step:
            abstract_touchers_dict = self.abstract_step_touchers.get(fluent_exp.fluent(), {})
            abstract_touchers = abstract_touchers_dict.get(fluent_exp, [])
        else:
            abstract_touchers_dict = self.abstract_step_touchers.get(fluent_exp.fluent(), {})
            abstract_touchers = chain(*abstract_touchers_dict.values())
        for b, t, e in abstract_touchers:
            if isinstance(b, DurativeAction):
                # if the action is durative, it might have started in the concrete steps and still
                # be relevant in the abstract steps (for example it still has to end)
                # TODO possible improvements?
                parameters_assignment = {}
                if self.ground_abstract_step:
                    lifted_ai = self.map_back_action_instance(b())
                    lifted_a, params_a = lifted_ai.action, lifted_ai.actual_parameters
                    parameters_assignment = dict(zip(map(self.em.ParameterExp, lifted_a.parameters), params_a))
                for k in range(1, h):
                    b_k_formula = [self.a(b, k)]
                    if self.ground_abstract_step:
                        parameters_equality = []
                        for param_exp, obj_exp in parameters_assignment.items():
                            parameters_equality.append(self.mgr.EqualsOrIff(self.to_smt(param_exp, k, k, scope=lifted_a), self.to_smt(obj_exp, k)))
                        b_k_formula.append(self.mgr.And(parameters_equality))
                    e_k_time = self.encode_tp(b, t, k, h)
                    b_k_formula.append(self.mgr.LT(last_t, e_k_time))
                    b_k_formula.append(self.mgr.LE(e_k_time, phi_time))
                    res.append(self.mgr.And(b_k_formula))

            h_step_formula = []
            if b is not None: # Instantaneous or Durative action
                h_step_formula = [self.a(b, h)]
                e_h_time = self.t_a(b, h) if t is None else self.encode_tp(b, t, h, h)
            else: # TIL
                e_h_time = self.encode_problem_tp(t, h)
            h_step_formula.append(self.mgr.LT(last_t, e_h_time))
            h_step_formula.append(self.mgr.LE(e_h_time, phi_time))
            res.append(self.mgr.And(h_step_formula))
        return self.mgr.Or(res)

    def _get_sorted_parameters(self, exp: FNode, action: Optional[Action]) -> Tuple[FNode, ...]:
        params = self.param_getter.get(exp)
        if action is None:
            assert not params
            return tuple()
        param_exps = map(self.em.ParameterExp, action.parameters)
        return tuple(filter(lambda x: x in params, param_exps))

    def _get_sorted_fve(self, exp: FNode) -> Tuple[FNode, ...]:
        fve = self.problem.environment.free_vars_extractor
        fluents = fve.get(exp)
        return tuple(sorted(fluents, key=str))
