from typing import Any, List, Optional, Tuple, Dict, Set
from tempest.encoders.base_encoder import BaseEncoder, Event
from unified_planning.model import DurativeAction, FNode, Fluent, Action, Timing, InstantaneousAction, StartTiming, GlobalEndTiming


class MonolithicEncoder(BaseEncoder):
    def encode_durative_action(self, action, i, h):
        l = []

        # Action duration constraints
        l.append(self.encode_action_duration(action, i))
        l.append(self.mgr.LE(self.mgr.Plus(self.t(i), self.dur(action, i)), self.t(h - 1)))

        # Action conditions
        for it, lc in action.conditions.items():
            c = self.em.And(lc)
            for k in range(i, h):
                l.append(self.encode_condition_or_goal(action, it, c, k, i))

        # Action effects
        for t, le in action.effects.items():
            if t.is_from_start() and t.delay == 0:
                l.append(self.encode_effects(action, t, le, i, i))
            else:
                l2 = []
                for k in range(i, h):
                    l2.append(self.encode_effects(action, t, le, k, i))
                l.append(self.mgr.Or(l2))

        return self.mgr.Implies(self.a(action, i), self.mgr.And(l))

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

    def encode_mutex_constraints(self, i, h):
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

        for (fluent_exp_a, action_a, timing_a, is_write_a, til_id_a), (fluent_exp_b, action_b, timing_b, is_write_b, til_id_b) in self._mutex_couples:
            for j in range(1, h):
                if i == j and action_a == action_b:
                    continue
                time_of_a = encode_timing(action_a, timing_a, i)
                time_of_b = encode_timing(action_b, timing_b, j)
                same_timing = self.mgr.Equals(time_of_a, time_of_b)

                if action_a is None:
                    if action_b is None:
                        # both are tils
                        res.append(self.mgr.Not(same_timing))
                    else:
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

    def _create_fluents_modification_map(self) -> Dict[Fluent, Dict[FNode, Set[Tuple[Optional[Action], Timing, bool, Optional[int]]]]]:
        # Create a map from a fluent to the event time that modifies that fluent
        # The values in the map represent:
        #   the action that contains the event (if None -> TILS or goal)
        #   the relative time (absolute if the action is None)
        #   True if the value is written by this event, False if it's red
        #   the ID of TILS, to prevent a til from being conflicting with itself
        # The returned map is a map from a lifted fluent to the mapping above (for efficiency)
        fluents_modification_map: Dict[Fluent, Dict[FNode, Set[Tuple[Optional[Action], Timing, bool, Optional[int]]]]] = {}

        # definition of macro to simplify the code
        fve = self.problem.environment.free_vars_extractor
        tils_id: List[int] = [0] # workaround to modify the out-of-scope counter in the "add_to_map" macro
        def add_to_map(fluent_exp, action, timing, is_write):
            til_id = None
            if action is None:
                til_id = tils_id[0]
                tils_id[0] = til_id + 1
            fluent = fluent_exp.fluent()
            modifications_map: Dict[FNode, Set[Tuple[Optional[Action], Timing, bool]]] = fluents_modification_map.setdefault(fluent, {})
            modifications_map.setdefault(fluent_exp, set()).add((action, timing, is_write, til_id))

        def add_expression_to_map(expression, action, timing):
            for x in fve.get(expression):
                add_to_map(x, action, timing, False)

        def add_effect_to_map(effect, action, timing):
            for x in effect.fluent.args:
                add_expression_to_map(x, action, timing)
            add_expression_to_map(effect.value, action, timing)
            add_expression_to_map(effect.condition, action, timing)
            add_to_map(effect.fluent, action, timing, True)

        start_timing = StartTiming()
        global_end_timing = GlobalEndTiming()

        for act in self.problem.actions:
            if isinstance(act, InstantaneousAction):
                for p in act.preconditions:
                    add_expression_to_map(p, act, start_timing)
                for eff in act.effects:
                    add_effect_to_map(eff, act, start_timing)
            else:
                assert isinstance(act, DurativeAction)
                for interval, cl in act.conditions.items():
                    for c in cl:
                        if not interval.is_left_open():
                            add_expression_to_map(c, act, interval.lower)
                        if not interval.is_right_open():
                            add_expression_to_map(c, act, interval.upper)

                for timing, el in act.effects.items():
                    for eff in el:
                        add_effect_to_map(eff, act, timing)

        for interval, cl in self.problem.timed_goals.items():
            for c in cl:
                if not interval.is_left_open():
                    add_expression_to_map(c, None, interval.lower)
                if not interval.is_right_open():
                    add_expression_to_map(c, None, interval.upper)

        for timing, el in self.problem.timed_effects.items():
            for eff in el:
                add_effect_to_map(eff, None, timing)

        for g in self.problem.goals:
            add_expression_to_map(g, None, global_end_timing)

        return fluents_modification_map

    def _get_mutex_couples(self) -> List[Tuple[Event, Event]]:
        mutex_couples: List[Tuple[Event, Event]] = []
        fluents_modification_map = self._create_fluents_modification_map()
        for fluent, modifications_map in fluents_modification_map.items():
            for fluent_exp_a, modifications_set_a in modifications_map.items():
                for action_a, timing_a, is_write_a, til_id_a in modifications_set_a:
                    for fluent_exp_b, modifications_set_b in modifications_map.items():
                        for action_b, timing_b, is_write_b, til_id_b in modifications_set_b:
                            if (not is_write_a and not is_write_b) or (til_id_a is not None and til_id_a == til_id_b):
                                continue
                            a_tup = (fluent_exp_a, action_a, timing_a, is_write_a, til_id_a)
                            b_tup = (fluent_exp_b, action_b, timing_b, is_write_b, til_id_b)
                            mutex_couples.append((a_tup, b_tup))

        return mutex_couples

    def encode_step_zero(self) -> Optional[Any]:
        return None

    def encode_step(self, step: int) -> Tuple[Any, Any]:
        res = []

        # Encode fluents initial values
        res.append(self.initial_state())

        # Timed effects
        for t, le in self.problem.timed_effects.items():
            l = []
            for i in range(1, step):
                l.append(self.encode_effects(None, t, le, i, 0))
            res.append(self.mgr.Or(l))

        for i in range(1, step):
            # Time is non-negative and strictly increasing
            res.append(self.mgr.LT(self.t(i - 1), self.t(i)))

            # Encode actions
            for a in self.problem.actions:
                if isinstance(a, InstantaneousAction):
                    res.append(self.encode_instantaneous_action(a, i))
                elif isinstance(a, DurativeAction):
                    res.append(self.encode_durative_action(a, i, step))

            # Frame axiom
            res.append(self.encode_frame_axiom(i))

            res.append(self.encode_mutex_constraints(i, step))

            res.append(self.encode_non_self_overlapping(i))

            # Add type constraints
            for c in self.symenc.type_constraints[i]:
                res.append(c)

        # Timed goals
        for it, lg in self.problem.timed_goals.items():
            g = self.em.And(lg)
            if it.lower == it.upper and it.lower.is_from_end() and it.lower.delay == 0:
                res.append(self.to_smt(g, step - 1))
            else:
                if it.lower.is_from_start() and it.lower.delay == 0:
                    res.append(self.to_smt(g, 0))
                for i in range(1, step):
                    res.append(self.encode_condition_or_goal(None, it, g, i, 0, step))
            res.append(self.mgr.LE(self.encode_problem_tp(it.upper), self.t(step - 1)))

        # Goals
        for g in self.problem.goals:
            res.append(self.to_smt(g, step - 1))

        return None, res
