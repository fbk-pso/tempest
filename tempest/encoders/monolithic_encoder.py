from itertools import chain
from typing import Any, Optional, Tuple
from tempest.encoders.base_encoder import BaseEncoder
from unified_planning.model import DurativeAction, InstantaneousAction, FNode, Fluent


class MonolithicEncoder(BaseEncoder):

    def condition_sat_in_abstract_step(self, action, it, c, w, h):
        last_concrete_step_time = self.t(h-1)
        if action is None:
            smt_tp_1 = self.encode_problem_tp(it.lower, h)
        else:
            smt_tp_1 = self.encode_tp(action, it.lower, w, h)
        start_condition_after_last_concrete_step = self.mgr.LT(last_concrete_step_time, smt_tp_1)
        condition_last_concrete_step = self.to_smt(c, h-1, w, action)
        condition_abstract_step = self.mgr.Or((self.fluent_mod(exp, action, w) for exp in self._get_sorted_free_vars(c)))
        return self.mgr.Implies(start_condition_after_last_concrete_step, self.mgr.Or(condition_last_concrete_step, condition_abstract_step))

    def encode_durative_action(self, action: DurativeAction, i: int, h: int):
        l = []

        # Action duration constraints
        l.append(self.encode_action_duration(action, i))
        if not self.optimal:
            l.append(self.mgr.LE(self.mgr.Plus(self.t(i), self.dur(action, i)), self.t(h - 1)))

        # Action conditions
        for it, lc in action.conditions.items():
            c = self.mgr.And(lc)
            for k in range(i, h):
                l.append(self.encode_condition_or_goal(action, it, c, k, i, h))
            if self.optimal:
                l.append(self.condition_sat_in_abstract_step(action, it, c, i, h))

        # Action effects
        for t, le in action.effects.items():
            if t.is_from_start() and t.delay == 0:
                effect_formula = self.encode_effects(action, t, le, i, i, h)
                if self.optimal:
                    smt_tp = self.encode_tp(action, t, i, h)
                    effect_in_abstract_step = self.mgr.LT(self.t(h-1), smt_tp)
                    effect_formula = self.mgr.Or(effect_formula, effect_in_abstract_step)
                l.append(effect_formula)
            else:
                l2 = []
                for k in range(i, h):
                    effect_formula = self.encode_effects(action, t, le, k, i, h)
                    if self.optimal:
                        smt_tp = self.encode_tp(action, t, i, h)
                        effect_in_abstract_step = self.mgr.LT(self.t(h-1), smt_tp)
                        effect_formula = self.mgr.Or(effect_formula, effect_in_abstract_step)
                    l2.append(effect_formula)
                if l2:
                    l.append(self.mgr.Or(l2))

        return self.mgr.Implies(self.a(action, i), self.mgr.And(l))

    def encode_step_zero(self) -> Optional[Any]:
        return None

    def encode_timed_goals(self, h: int, optimal: bool):
        res = []
        for it, lg in self.problem.timed_goals.items():
            g = self.em.And(lg)
            if it.lower == it.upper and it.lower.is_from_end() and it.lower.delay == 0:
                res.append(self.to_smt(g, h - 1))
            else:
                if it.lower.is_from_start() and it.lower.delay == 0:
                    res.append(self.to_smt(g, 0))
                for i in range(1, h):
                    res.append(self.encode_condition_or_goal(None, it, g, i, 0, h))
                if self.optimal:
                    res.append(self.condition_sat_in_abstract_step(None, it, g, None, h))
            if not optimal:
                res.append(self.mgr.LE(self.encode_problem_tp(it.upper, h), self.t(h - 1)))
        return self.mgr.And(res)

    def encode_fluent_mod_formula(self, fluent: Fluent, fluent_exp: Optional[FNode], h: int):
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

        return self.mgr.Or(res)

    def encode_step(self, h: int) -> Tuple[Any, Any]:
        res = []

        # Encode fluents initial values
        res.append(self.initial_state())

        # Timed effects
        for t, le in self.problem.timed_effects.items():
            l = []
            for i in range(1, h):
                effect_formula = self.encode_effects(None, t, le, i, 0, h)
                if self.optimal:
                    smt_tp = self.encode_problem_tp(t, None)
                    effect_in_abstract_step = self.mgr.LT(self.t(h-1), smt_tp)
                    effect_formula = self.mgr.Or(effect_formula, effect_in_abstract_step)
                l.append(effect_formula)
            res.append(self.mgr.Or(l))

        for i in range(1, h):

            # Encode actions
            for a in self.problem.actions:
                if isinstance(a, InstantaneousAction):
                    res.append(self.encode_instantaneous_action(a, i))
                elif isinstance(a, DurativeAction):
                    res.append(self.encode_durative_action(a, i, h))

            res.append(self.encode_increasing_time(i))

            # Mutex constraints
            for j in range(1, h):
                res.append(self.encode_mutex_constraints(i, j, h))

            # Self-Overlapping
            if not self.problem.self_overlapping:
                res.append(self.encode_non_self_overlapping(i))

            # Frame axiom
            res.append(self.encode_frame_axiom(i, h))

            # Add type constraints
            res.extend(self.symenc.type_constraints[i])

        if self.optimal:
            # Encode actions
            for a in self.abstract_step_actions:
                if isinstance(a, InstantaneousAction):
                    res.append(self.encode_abstract_instantaneous_action(a, h))
                elif isinstance(a, DurativeAction):
                    res.append(self.encode_durative_action(a, h, h))

            res.append(self.encode_density_constraints(h))
            res.append(self.phi_sched(h))

        res.append(self.encode_timed_goals(h, self.optimal))

        # Goals
        for g in self.problem.goals:
            goal_formula = self.to_smt(g, h - 1)
            if self.optimal:
                goal_formula = self.mgr.Or(chain([goal_formula], (self.fluent_mod(exp, None, None) for exp in self._get_sorted_free_vars(g))))
            res.append(goal_formula)

        # fluent_mod variables
        for fluent_mod_var, (fluent, fluent_exp) in self.fluent_mod_var.items():
            res.append(self.mgr.Iff(fluent_mod_var, self.encode_fluent_mod_formula(fluent, fluent_exp, h)))

        return None, res

    def encode_density_constraints(self, h: int):
        return self.mgr.Implies(self.uses_abstact_step(h), self.mgr.And([self.encode_density_constraint(i) for i in range(1, h)]))
