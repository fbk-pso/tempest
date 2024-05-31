from functools import lru_cache
from itertools import chain
from typing import Any, Dict, List, Optional, Tuple
from tempest.encoders.base_encoder import BaseEncoder
from unified_planning.model import DurativeAction, InstantaneousAction, MinimizeActionCosts, FNode, Action, Timing
from pysmt.optimization.goal import MaxSMTGoal, MinMaxGoal


class MonolithicEncoder(BaseEncoder):
    def encode_durative_action(self, action: DurativeAction, i: int, h: int):
        l = []

        # Action duration constraints
        l.append(self.encode_action_duration(action, i))
        if not self.optimal:
            l.append(self.mgr.LE(self.mgr.Plus(self.t(i), self.dur(action, i)), self.t(h - 1)))

        # Action conditions
        for it, lc in action.conditions.items():
            for c in lc:
                for k in range(i, h):
                    l.append(self.encode_condition_or_goal(action, it, c, k, i, h))

        # Action effects
        for t, le in action.effects.items():
            if t.is_from_start() and t.delay == 0:
                l.append(self.encode_effects(action, t, le, i, i, h))
            else:
                l2 = []
                for k in range(i, h):
                    l2.append(self.encode_effects(action, t, le, k, i, h))
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
            if not optimal:
                res.append(self.mgr.LE(self.encode_problem_tp(it.upper, h), self.t(h - 1)))
        return self.mgr.And(res)

    def encode_step(self, h: int) -> Tuple[Any, Any]:
        res = []

        # Encode fluents initial values
        res.append(self.initial_state())

        # Timed effects
        for t, le in self.problem.timed_effects.items():
            l = []
            for i in range(1, h):
                l.append(self.encode_effects(None, t, le, i, 0, h))
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
                goal_formula = self.mgr.Or(chain([goal_formula], (self.fluent_mod(exp, None, None, h) for exp in self._get_sorted_free_vars(g))))
            res.append(goal_formula)

        # fluent_mod variables
        for fluent_mod_value, fluent_mod_var in self.fluent_mod_formulae_mapping.items():
            res.append(self.mgr.Iff(fluent_mod_var, fluent_mod_value))

        return None, res

    def objective_to_minimize(self, h: int):
        assert len(self.problem.quality_metrics) < 2, "Problem has more than one quality metric"
        metric = self.problem.quality_metrics[0] if self.problem.quality_metrics else None
        if metric is None or metric.is_minimize_makespan():
            terms = [self.t(h-1)]
            timed_goals_timings = chain(*map(lambda x: (x.lower, x.upper), self.problem.timed_goals.keys()))
            problem_timings = chain(timed_goals_timings, self.problem.timed_effects.keys())
            for timing in filter(lambda x: x.is_from_start(), problem_timings):
                assert isinstance(timing, Timing)
                terms.append(self.encode_problem_tp(timing, h))
            for a in self.abstract_step_actions:
                t_a = self.t_a(a, h)
                if isinstance(a, InstantaneousAction):
                    terms.append(t_a)
                else:
                    terms.append(self.mgr.Plus(t_a, self.dur(a, h)))
            return MinMaxGoal(terms), None
        elif metric.is_minimize_action_costs():
            return self._get_max_smt_goal(metric, h), None
        else:
            raise NotImplementedError(f"Metric {metric} not supported")

    def _get_max_smt_goal(self, metric, h: int) -> MaxSMTGoal:
        goal = MaxSMTGoal()
        range_lim = h if self.ground_abstract_step else h+1
        for a in self.problem.actions:
            for assignments, cost in self._get_action_costs(metric, a):
                weight = cost.constant_value()
                for i in range(range_lim):
                    clauses = [self.a(a, i)]
                    for param_exp, obj_exp in assignments.items():
                        assert param_exp.is_parameter_exp()
                        clauses.append(self.mgr.EqualsOrIff(self.to_smt(param_exp, i, scope=a), self.to_smt(obj_exp, i)))
                    goal.add_soft_clause(self.mgr.Not(self.mgr.And(clauses)), weight)

        # The cost of the action in the abstract step must be added
        if self.ground_abstract_step:
            grounded_metric = self.abstract_step_metrics[0]
            assert grounded_metric.is_minimize_action_costs()
            for a in self.abstract_step_actions:
                cost = self.simplifier.simplify(grounded_metric.get_action_cost(a))
                weight = cost.constant_value()
                goal.add_soft_clause(self.mgr.Not(self.a(a, h)), weight)
        return goal

    @lru_cache(maxsize=None)
    def _get_action_costs(self, metric: MinimizeActionCosts, action: Action) -> List[Tuple[Dict[FNode, FNode], FNode]]:
        # This method takes the metric and the action and returns a list
        # containing  Tuples, each Tuple contains 2 element, the first one is
        # a Dictionary that contains as keys the action parameters and
        # as values the object used to ground the action and generate a constant cost
        #
        # One important note is that this method does not generate every possible grounding of
        # the action, but only grounds the parameters that are actually involved in the cost
        assert isinstance(metric, MinimizeActionCosts)
        cost = self.simplifier.simplify(metric.get_action_cost(action))
        if cost.is_constant(): # cost does not depend on parameters
            return [({}, cost)]
        res = []
        cost_parameters = self._get_sorted_parameters(cost, action)
        for parameters_value in self._get_possible_parameters_assignments(cost_parameters):
            assignments = dict(zip(cost_parameters, parameters_value))
            grounded_cost = self.simplifier.simplify(cost.substitute(assignments))
            assert grounded_cost.is_constant(), f"Non constant expression detected in ActionCosts: {action.name}, {metric.get_action_cost(action)}"
            res.append((assignments, grounded_cost))
        return res

    def encode_density_constraints(self, h: int):
        assert self.optimal
        res = []
        for i in range(1, h):
            sub_res = []
            t_i = self.t(i)

            for t in self.problem.timed_effects.keys():
                sub_res.append(self.mgr.Equals(self.encode_problem_tp(t, h), t_i))

            for act in self.problem.actions:
                sub_res.append(self.a(act, i))
                if isinstance(act, DurativeAction):
                    for s in range(1, i):
                        a_s = self.a(act, s)
                        for t in act.effects.keys():
                            effect_at_t_i = self.mgr.Equals(self.encode_tp(act, t, s, h), t_i)
                            sub_res.append(self.mgr.And(a_s, effect_at_t_i))
            res.append(self.mgr.Or(sub_res))

        return self.mgr.Implies(self._uses_abstact_step(h), self.mgr.And(res))

    def _uses_abstact_step(self, h: int):
        res = []

        last_concrete_step_time = self.t(h-1)
        for g in self.problem.goals:
            res.append(self.to_smt(g, h-1))

        res.append(self.encode_timed_goals(h, False))

        for t in self.problem.timed_effects.keys():
            res.append(self.mgr.LE(self.encode_problem_tp(t, h), last_concrete_step_time))

        for act in self.problem.actions:
            if isinstance(act, DurativeAction):
                for i in range(1, h):
                    a_i = self.a(act, i)
                    end_a_i = self.mgr.Plus(self.t(i), self.dur(act, i))
                    ends_before_abstract = self.mgr.LE(end_a_i, last_concrete_step_time)
                    res.append(self.mgr.Implies(a_i, ends_before_abstract))

        return self.mgr.Not(self.mgr.And(res))
