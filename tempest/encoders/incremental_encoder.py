from typing import Any, Optional
from tempest.encoders.base_encoder import BaseEncoder

from unified_planning.model import DurativeAction, InstantaneousAction


class IncrementalEncoder(BaseEncoder):
    def __init__(self, problem, pysmt_env=None):
        super().__init__(problem, pysmt_env)

    def chain_var(self, action, e, i, w):
        return self.symenc.chain_var(action, e, i, w)

    def encode_incremental_durative_action(self, action, i):
        l = []
        temp_l = []

        conjunction = []
        conjunction.append(self.encode_action_duration(action, i))
        conjunction.append(
            self.mgr.LE(self.mgr.Plus(self.t(i), self.dur(action, i)), self.t_last())
        )

        # Action conditions
        for it, lc in action.conditions.items():
            c = self.em.And(lc)
            ev = (it, c)
            conjunction.append(self.chain_var(action, ev, i, i))
            for w in range(1, i + 1):
                temp_l.append(
                    self.mgr.Implies(
                        self.chain_var(action, ev, i + 1, w), self.mgr.Bool(True)
                    )
                )
                rhs = self.encode_tp(action, it.upper, w)
                l.append(
                    self.mgr.Implies(self.a(action, w), self.mgr.LE(rhs, self.t_last()))
                )
                formula = self.encode_condition_or_goal(action, it, c, i, w, None)
                l.append(
                    self.mgr.Implies(
                        self.chain_var(action, ev, i, w),
                        self.mgr.And(formula, self.chain_var(action, ev, i + 1, w)),
                    )
                )

        # Action effects
        for t, le in action.effects.items():
            ev = (t, tuple(le))
            conjunction.append(self.chain_var(action, ev, i, i))
            for w in range(1, i + 1):
                temp_l.append(
                    self.mgr.Implies(
                        self.chain_var(action, ev, i + 1, w), self.mgr.Bool(False)
                    )
                )
                formula = self.encode_effects(action, t, le, i, w)
                l.append(
                    self.mgr.Implies(
                        self.chain_var(action, ev, i, w),
                        self.mgr.Or(formula, self.chain_var(action, ev, i + 1, w)),
                    )
                )

        l.append(self.mgr.Implies(self.a(action, i), self.mgr.And(conjunction)))

        return self.mgr.And(l), self.mgr.And(temp_l)

    def encode_step_zero(self) -> Optional[Any]:
        res = []

        # Encode fluents initial values
        res.append(self.initial_state())

        # Timed effects
        for t, le in self.problem.timed_effects.items():
            ev = (t, tuple(le))
            res.append(self.chain_var(None, ev, 1, 0))

        # Timed goals
        for it, lg in self.problem.timed_goals.items():
            g = self.em.And(lg)
            if it.lower.is_from_start() and it.lower.delay == 0:
                res.append(self.to_smt(g, 0, 0, scope=None))

        return self.mgr.And(res)

    def encode_step(self, i):
        res = []
        temp_res = []

        res.append(self.encode_increasing_time(i))

        temp_res.append(self.mgr.Equals(self.t_last(), self.t(i)))

        # Timed effect
        for t, le in self.problem.timed_effects.items():
            assert t.is_from_start()
            ev = (t, tuple(le))
            formula = self.encode_effects(None, t, le, i, 0)
            res.append(
                self.mgr.Implies(
                    self.chain_var(None, ev, i, 0),
                    self.mgr.Or(formula, self.chain_var(None, ev, i + 1, 0)),
                )
            )
            temp_res.append(
                self.mgr.Implies(
                    self.chain_var(None, ev, i + 1, 0), self.mgr.Bool(False)
                )
            )

        # Actions
        for a in self.problem.actions:
            if isinstance(a, InstantaneousAction):
                res.append(self.encode_instantaneous_action(a, i))
            elif isinstance(a, DurativeAction):
                f, tf = self.encode_incremental_durative_action(a, i)
                res.append(f)
                temp_res.append(tf)

        # Frame axiom
        res.append(self.encode_frame_axiom(i, None))

        # Non Self-Overlapping
        if not self.problem.self_overlapping:
            res.append(self.encode_non_self_overlapping(i))

        # Mutex constraints
        for j in range(1, i+1):
            res.append(self.encode_mutex_constraints(j, i, h=None))
            res.append(self.encode_mutex_constraints(i, j, h=None))

        # Add type constraints
        for c in self.symenc.type_constraints[i]:
            res.append(c)

        # Timed goals
        for it, lg in self.problem.timed_goals.items():
            g = self.em.And(lg)
            if it.lower == it.upper and it.lower.is_from_end() and it.lower.delay == 0:
                temp_res.append(self.to_smt(g, i, 0))
            else:
                res.append(self.encode_condition_or_goal(None, it, g, i, 0, None))
                res.append(self.mgr.LE(self.encode_problem_tp(it.upper, None), self.t_last()))

        # Goals
        temp_res.append(
            self.to_smt(self.em.And(self.problem.goals), i, 0, scope=None)
        )

        return self.mgr.And(res), temp_res
