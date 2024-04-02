from typing import Any, Optional, Tuple
from tempest.encoders.base_encoder import BaseEncoder
from unified_planning.model import DurativeAction, InstantaneousAction


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
                l.append(self.encode_condition_or_goal(action, it, c, k, i, h))

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

    def encode_step_zero(self) -> Optional[Any]:
        return None

    def encode_step(self, h: int) -> Tuple[Any, Any]:
        res = []

        # Encode fluents initial values
        res.append(self.initial_state())

        # Timed effects
        for t, le in self.problem.timed_effects.items():
            l = []
            for i in range(1, h):
                l.append(self.encode_effects(None, t, le, i, 0))
            res.append(self.mgr.Or(l))

        for i in range(1, h):
            res.append(self.encode_increasing_time(i))

            # Encode actions
            for a in self.problem.actions:
                if isinstance(a, InstantaneousAction):
                    res.append(self.encode_instantaneous_action(a, i))
                elif isinstance(a, DurativeAction):
                    res.append(self.encode_durative_action(a, i, h))

            # Frame axiom
            res.append(self.encode_frame_axiom(i, h))

            # Mutex constraints
            for j in range(1, h):
                res.append(self.encode_mutex_constraints(i, j, h))

            # Self-Overlapping
            if not self.problem.self_overlapping:
                res.append(self.encode_non_self_overlapping(i))

            # Add type constraints
            for c in self.symenc.type_constraints[i]:
                res.append(c)

        # Timed goals
        for it, lg in self.problem.timed_goals.items():
            g = self.em.And(lg)
            if it.lower == it.upper and it.lower.is_from_end() and it.lower.delay == 0:
                res.append(self.to_smt(g, h - 1))
            else:
                if it.lower.is_from_start() and it.lower.delay == 0:
                    res.append(self.to_smt(g, 0))
                for i in range(1, h):
                    res.append(self.encode_condition_or_goal(None, it, g, i, 0, h))
            res.append(self.mgr.LE(self.encode_problem_tp(it.upper, h), self.t(h - 1)))

        # Goals
        for g in self.problem.goals:
            res.append(self.to_smt(g, h - 1))

        return None, res
