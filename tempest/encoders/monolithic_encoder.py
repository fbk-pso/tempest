from functools import lru_cache
from itertools import chain
from typing import Any, Optional, Tuple
from tempest.encoders.base_encoder import BaseEncoder
from unified_planning.model import DurativeAction, InstantaneousAction
from unified_planning.model.walkers import QuantifierSimplifier
from pysmt.optimization.goal import MinimizationGoal, MaxSMTGoal


class MonolithicEncoder(BaseEncoder):
    def encode_durative_action(self, action, i, h):
        l = []

        # Action duration constraints
        l.append(self.encode_action_duration(action, i))
        # print(f"Action {action.name} step {i} duration: {l[-1].serialize()}\n")
        if not self.optimal:
            l.append(self.mgr.LE(self.mgr.Plus(self.t(i), self.dur(action, i)), self.t(h - 1)))

        # Action conditions
        for it, lc in action.conditions.items():
            # c = self.em.And(lc) # TODO get back to this c instead of the for loop below
            for c in lc:
                for k in range(i, h):
                    l.append(self.encode_condition_or_goal(action, it, c, k, i, h=h, optimal=self.optimal))
                    # l.append(self.encode_condition_or_goal(action, it, c, k, i))
                    # print(f"Action condition {c} at step {k}: {l[-1].serialize()}\n")

        # Action effects
        for t, le in action.effects.items():
            if t.is_from_start() and t.delay == 0:
                l.append(self.encode_effects(action, t, le, i, i, h))

                # print(f"Action {action.name} {t} effects: {l[-1].serialize()}\n")
            else:
                l2 = []
                for k in range(i, h):
                    l2.append(self.encode_effects(action, t, le, k, i, h))
                if l2:
                    l.append(self.mgr.Or(l2))
                    # print(f"Action {action.name} {t} effects: {l[-1].serialize()}\n")

        return self.mgr.Implies(self.a(action, i), self.mgr.And(l))

    def encode_step_zero(self) -> Optional[Any]:
        return None

    def _uses_abstact_step(self, h):
        res = []

        last_concrete_step_time = self.t(h-1)
        for g in self.problem.goals:
            res.append(self.to_smt(g, h-1))

        res.append(self.encode_timed_goals(h, False))

        for t in self.problem.timed_effects.keys():
            res.append(self.mgr.LE(self.encode_problem_tp(t), last_concrete_step_time))

        for act in self.problem.actions:
            if isinstance(act, DurativeAction):
                for i in range(1, h):
                    a_i = self.a(act, i)
                    end_a_i = self.mgr.Plus(self.t(i), self.dur(act, i))
                    ends_before_abstract = self.mgr.LE(end_a_i, last_concrete_step_time)
                    res.append(self.mgr.Implies(a_i, ends_before_abstract))
            # TODO understand if those are needed
            a_h = self.a(act, h)
            res.append(self.mgr.Not(a_h))

        return self.mgr.Not(self.mgr.And(res))

    def encode_density_constraints(self, h: int):
        assert self.optimal
        res = []
        for i in range(1, h):
            sub_res = []
            t_i = self.t(i)

            for t in self.problem.timed_effects.keys():
                sub_res.append(self.mgr.Equals(self.encode_problem_tp(t), t_i)) # TODO check if use EqualsOrIff

            for act in self.problem.actions:
                sub_res.append(self.a(act, i))
                if isinstance(act, DurativeAction):
                    for s in range(1, i):
                        a_s = self.a(act, s)
                        for t in act.effects.keys():
                            effect_at_t_i = self.mgr.Equals(self.encode_tp(act, t, s), t_i)
                            sub_res.append(self.mgr.And(a_s, effect_at_t_i))
            res.append(self.mgr.Or(sub_res))

        return self.mgr.Implies(self._uses_abstact_step(h), self.mgr.And(res))

    def encode_timed_goals(self, h, optimal):
        res = []
        for it, lg in self.problem.timed_goals.items():
            g = self.em.And(lg)
            if it.lower == it.upper and it.lower.is_from_end() and it.lower.delay == 0:
                res.append(self.to_smt(g, h - 1))
            else:
                if it.lower.is_from_start() and it.lower.delay == 0:
                    res.append(self.to_smt(g, 0))
                for i in range(1, h):
                    res.append(self.encode_condition_or_goal(None, it, g, i, 0, h, optimal=optimal))
            if optimal:
                assert self.optimal
                res.append(self.mgr.LE(self.encode_problem_tp(it.upper, h), self.t(h - 1)))
        return self.mgr.And(res)

    def encode_step(self, h: int) -> Tuple[Any, Any]:
        res = []

        # Encode fluents initial values
        res.append(self.initial_state())

        # print(f"initial state: {res[-1].serialize()}\n")

        # Timed effects
        for t, le in self.problem.timed_effects.items():
            l = []
            for i in range(1, h):
                l.append(self.encode_effects(None, t, le, i, 0, h))
            res.append(self.mgr.Or(l))
            # print(f"timed effects: {res[-1].serialize()}\n")

        for i in range(1, h+1):

            # Encode actions
            for a in self.problem.actions:
                if isinstance(a, InstantaneousAction):
                    if self.optimal:
                        res.append(self.encode_optimal_instantaneous_action(a, i, h))
                    else:
                        res.append(self.encode_instantaneous_action(a, i))
                elif isinstance(a, DurativeAction):
                    res.append(self.encode_durative_action(a, i, h))
                # print(f"{a.name} formula {i}: {res[-1].serialize()}\n")

            if i < h:
                res.append(self.encode_increasing_time(i))
                # print(f"increasing_time{i}: {res[-1].serialize()}\n")

                # Mutex constraints
                for j in range(1, h):
                    res.append(self.encode_mutex_constraints(i, j, h))

                    # print(f"mutex_constraints {i}, {j}: {res[-1].serialize()}\n")

                # Self-Overlapping
                if not self.problem.self_overlapping:
                    res.append(self.encode_non_self_overlapping(i))

                    # print(f"non self-overlapping {i}: {res[-1].serialize()}\n")

                # Frame axiom
                res.append(self.encode_frame_axiom(i, h))
                # print(f"frame axiom {i}: {res[-1].serialize()}\n")

                # Add type constraints
                res.extend(self.symenc.type_constraints[i])
                # for j, c in enumerate(self.symenc.type_constraints[i]):
                #     # print(f"type constraints {i}, {j}: {c}\n")

        if self.optimal:
            res.append(self.encode_density_constraints(h))
            # print(f"density_constraints {h}: {res[-1].serialize()}\n")

        res.append(self.encode_timed_goals(h, self.optimal))

        # print(f"timed goals {h}: {res[-1].serialize()}\n")

        # Goals
        fve = self.problem.environment.free_vars_extractor
        for g in self.problem.goals:
            goal_formula = self.to_smt(g, h - 1)
            if self.optimal:
                goal_formula = self.mgr.Or(chain([goal_formula], (self.fluent_mod(exp.fluent(), h) for exp in fve.get(g))))
            res.append(goal_formula)
            # print(f"goal {g}: {res[-1].serialize()}\n")

        return None, res

    def objective_to_minimize(self, h: int):
        assert len(self.problem.metrics) < 2, "Problem has more than one quality metric"
        metric = self.problem.metrics[-1] if self.problem.metrics else None
        if metric is None or metric.is_minimize_makespan():
            return MinimizationGoal(self.t(h-1)), None
        assert metric.is_minimize_action_costs(), f"Metric {metric} not supported"

    @lru_cache(maxsize=None)
    def _get_action_costs(self):
        simplifier = QuantifierSimplifier(self.problem.environment, self.problem)

        ass = self.problem.initial_values


#TODO in optimal case, t_h_a have to be added.
