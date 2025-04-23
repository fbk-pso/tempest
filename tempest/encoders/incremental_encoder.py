# Copyright (C) 2025 PSO Unit, Fondazione Bruno Kessler
# This file is part of TemPEST.
#
# TemPEST is free software: you can redistribute it and/or modify
# it under the terms of the GNU Lesser General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# TemPEST is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public License
# along with this program. If not, see <https://www.gnu.org/licenses/>.
#

from functools import lru_cache
from itertools import chain
from typing import Any, Optional
from tempest.encoders.base_encoder import BaseEncoder

from unified_planning.model import DurativeAction, InstantaneousAction
from unified_planning.model.fluent import get_all_fluent_exp


class IncrementalEncoder(BaseEncoder):

    def chain_var(self, action, e, i, w):
        return self.symenc.chain_var(action, e, i, w)

    @lru_cache(maxsize=None)
    def vcg(self):
        return self.mgr.FreshSymbol(template="vcg%d")

    def encode_incremental_durative_action(self, action, i):
        l = []
        temp_l = []

        conjunction = []
        conjunction.append(self.encode_action_duration(action, i))
        if not self.optimal:
            conjunction.append(
                self.mgr.LE(self.mgr.Plus(self.t(i), self.dur(action, i)), self.t_last())
            )

        # Action conditions
        for it, lc in action.conditions.items():
            c = self.em.And(lc)
            ev = (it, c)
            conjunction.append(self.chain_var(action, ev, i, i))
            for w in range(1, i + 1):
                if self.optimal:
                    smt_tp_1 = self.encode_tp(action, it.lower, w, None)
                    if it.is_left_open():
                        start_condition_after_last_concrete_step = self.mgr.LE(self.t_last(), smt_tp_1)
                    else:
                        start_condition_after_last_concrete_step = self.mgr.LT(self.t_last(), smt_tp_1)
                    condition_last_concrete_step = self.to_smt(c, i, w, action)
                    condition_abstract_step = self.mgr.Or((self.fluent_mod(exp, action, w) for exp in self._get_sorted_free_vars(c)))
                    temp_l.append(
                        self.mgr.Implies(
                            self.chain_var(action, ev, i + 1, w),
                            self.mgr.Implies(start_condition_after_last_concrete_step, self.mgr.Or(condition_last_concrete_step, condition_abstract_step))
                        )
                    )
                else:
                    temp_l.append(
                        self.mgr.Implies(
                            self.chain_var(action, ev, i + 1, w), self.mgr.Bool(True)
                        )
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
                if self.optimal:
                    smt_tp_1 = self.encode_tp(action, t, w, None)
                    temp_l.append(
                        self.mgr.Implies(
                            self.chain_var(action, ev, i + 1, w),
                            self.mgr.GT(smt_tp_1, self.t_last())
                        )
                    )
                else:
                    temp_l.append(
                        self.mgr.Implies(
                            self.chain_var(action, ev, i + 1, w), self.mgr.Bool(False)
                        )
                    )
                formula = self.encode_effects(action, t, le, i, w, None)
                l.append(
                    self.mgr.Implies(
                        self.chain_var(action, ev, i, w),
                        self.mgr.Or(formula, self.chain_var(action, ev, i + 1, w)),
                    )
                )

        l.append(self.mgr.Implies(self.a(action, i), self.mgr.And(conjunction)))

        return self.mgr.And(l), self.mgr.And(temp_l)

    def encode_abstract_durative_action(self, action, i):
        temp_l = []

        temp_l.append(self.encode_action_duration(action, i)) # TOFIX if non-static fluents in duration

        # Action conditions
        for it, lc in action.conditions.items():
            c = self.em.And(lc)
            condition_last_concrete_step = self.to_smt(c, i-1, i, scope=action)
            condition_abstract_step = self.mgr.Or((self.fluent_mod(exp, action, i) for exp in self._get_sorted_free_vars(c)))
            temp_l.append(self.mgr.Implies(self.mgr.GT(self.encode_tp(action, it.lower, i, None, True), self.t_last()), self.mgr.Or(condition_last_concrete_step, condition_abstract_step)))

        # Action effects
        for t, _ in action.effects.items():
            temp_l.append(self.mgr.GT(self.encode_tp(action, t, i, None, True), self.t_last()))

        return self.mgr.Implies(self.a(action, i), self.mgr.And(temp_l))

    def encode_fluent_mod_formula_step_zero(self, fluent, fluent_exp):
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
                til_in_abstract_step = self.mgr.GT(self.encode_problem_tp(timing, None), self.t_last())
                res.append(til_in_abstract_step)
            else:
                ev = (timing, eff)
                res.append(self.chain_var(action, ev, 1, 0))

        return self.mgr.Or(res)

    def encode_fluent_mod_formula(self, fluent, fluent_exp, i):
        assert not (self.ground_abstract_step and self.param_getter.get(fluent_exp))
        res = []
        temp_res = []
        abstract_fluent_touchers = self.abstract_step_touchers.get(fluent, None)
        if abstract_fluent_touchers is None:
            return self.mgr.TRUE(), self.mgr.TRUE()

        if self.ground_abstract_step:
            assert fluent_exp is not None
            fluent_touchers_gen = abstract_fluent_touchers.get(fluent_exp, [])
        else:
            assert fluent_exp is None
            fluent_touchers_gen = chain(*abstract_fluent_touchers.values())

        for action, timing, eff in fluent_touchers_gen:
            if action is None:
                continue
            ev = (timing, eff)
            if timing is None:
                res.append(self.mgr.Implies(self.chain_var(action, ev, i, 0), self.chain_var(action, ev, i+1, 0)))
                temp_res.append(self.mgr.Implies(self.chain_var(action, ev, i+1, 0), self.a(action, i+1)))
            else:
                concrete_action, parameters_assignment = action, {}
                if self.ground_abstract_step:
                    concrete_ai = self.map_back_action_instance(action())
                    concrete_action = concrete_ai.action
                    parameters_assignment = dict(zip(concrete_action.parameters, concrete_ai.actual_parameters))
                a_i = self.a(concrete_action, i)
                parameters_equality = []
                for param_exp, obj_exp in parameters_assignment.items():
                    parameters_equality.append(self.mgr.EqualsOrIff(self.to_smt(self.em.ParameterExp(param_exp), i, i, scope=concrete_action), self.to_smt(obj_exp, i)))
                p_eq = self.mgr.And(parameters_equality)
                effect_time = self.encode_tp(concrete_action, timing, i, None)
                effect_in_abstract_step = self.mgr.GT(effect_time, self.t_last())
                effect_performed_in_abstract_step = self.mgr.And(a_i, p_eq, effect_in_abstract_step)
                res.append(self.mgr.Implies(self.chain_var(action, ev, i, 0), self.mgr.Or(effect_performed_in_abstract_step, self.chain_var(action, ev, i+1, 0))))
                temp_res.append(self.mgr.Implies(self.chain_var(action, ev, i+1, 0), self.a(action, i+1)))

        return self.mgr.And(res), self.mgr.And(temp_res)


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

        if self.ground_abstract_step:
            for fluent in self.problem.fluents:
                for fluent_exp in get_all_fluent_exp(self.problem, fluent):
                    mod_f = self._fluent_mod(fluent, fluent_exp)
                    res.append(self.mgr.Iff(mod_f, self.encode_fluent_mod_formula_step_zero(fluent, fluent_exp)))
        else:
            for fluent in self.problem.fluents:
                mod_f = self._fluent_mod(fluent, None)
                res.append(self.mgr.Iff(mod_f, self.encode_fluent_mod_formula_step_zero(fluent, None)))

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
            formula = self.encode_effects(None, t, le, i, 0, None)
            res.append(
                self.mgr.Implies(
                    self.chain_var(None, ev, i, 0),
                    self.mgr.Or(formula, self.chain_var(None, ev, i + 1, 0)),
                )
            )
            if self.optimal:
                smt_tp = self.encode_problem_tp(t, None)
                temp_res.append(
                    self.mgr.Implies(
                        self.chain_var(None, ev, i + 1, 0), self.mgr.GT(smt_tp, self.t_last())
                    )
                )
            else:
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
            if i != j:
                res.append(self.encode_mutex_constraints(i, j, h=None))

        # Add type constraints
        for c in self.symenc.type_constraints.get(i, []):
            res.append(c)

        if self.optimal:
            res.append(self.mgr.Implies(self.vcg(), self.encode_density_constraint(i)))
            for a in self.abstract_step_actions:
                if isinstance(a, InstantaneousAction):
                    temp_res.append(self.encode_abstract_instantaneous_action(a, i+1))
                elif isinstance(a, DurativeAction):
                    temp_res.append(self.encode_abstract_durative_action(a, i+1))
            temp_res.append(self.mgr.Iff(self.vcg(), self.uses_abstact_step(i, None)))
            temp_res.append(self.phi_sched(i+1))

        # Timed goals
        for it, lg in self.problem.timed_goals.items():
            g = self.em.And(lg)
            if it.lower == it.upper and it.lower.is_from_end() and it.lower.delay == 0:
                if self.optimal:
                    temp_res.append(self.mgr.Or((self.fluent_mod(exp, None, None) for exp in self._get_sorted_free_vars(g)), self.to_smt(g, i, 0)))
                else:
                    temp_res.append(self.to_smt(g, i, 0))
            else:
                res.append(self.encode_condition_or_goal(None, it, g, i, 0, None))
                if self.optimal:
                    mod_f = self.mgr.Or((self.fluent_mod(exp, None, None) for exp in self._get_sorted_free_vars(g)))
                    temp_res.append(self.mgr.Implies(self.mgr.LT(self.t(i), self.encode_problem_tp(it.lower, None)), self.mgr.Or(mod_f, self.to_smt(g, i, 0))))
                else:
                    res.append(self.mgr.LE(self.encode_problem_tp(it.upper, None), self.t_last()))

        # Goals
        if self.optimal:
            for goal in self.problem.goals:
                goals = goal.args if goal.is_and() else [goal]
                for g in goals:
                    temp_res.append(self.mgr.Or([self.fluent_mod(exp, None, None) for exp in self._get_sorted_free_vars(g)] + [self.to_smt(g, i, 0)]))
        else:
            temp_res.append(
                self.to_smt(self.em.And(self.problem.goals), i, 0, scope=None)
            )

        # fluent_mod variables
        if self.optimal:
            for mod_f, (fluent, fluent_exp) in self.fluent_mod_var.items():
                f, t_f = self.encode_fluent_mod_formula(fluent, fluent_exp, i)
                res.append(f)
                temp_res.append(t_f)

        return self.mgr.And(res), temp_res
