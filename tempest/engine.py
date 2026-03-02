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

from fractions import Fraction
from time import time
import pysmt
import warnings
import unified_planning as up

import sys

from unified_planning.model import ProblemKind
from unified_planning.engines import (
    PlanGenerationResultStatus,
    PlanGenerationResult,
    Credits,
)
from typing import IO, Callable, Iterator, Optional
from tempest.encoders import MonolithicEncoder, IncrementalEncoder


credits = Credits(
    "TemPEST",
    "FBK PSO Unit",
    "tamer@fbk.eu",
    "https://github.com/fbk-pso/tempest",
    "LGPLv3",
    "Temporal Planning Encoding into Satisfiability Testing",
    "Temporal Planner that encodes temporal planning problems into SAT/SMT formulations",
)


class _BaseEngine(up.engines.Engine, up.engines.mixins.OneshotPlannerMixin):
    """Implementation of the base tempest engine."""

    def __init__(self, incremental=True, horizon=None, solver_name=None):
        up.engines.Engine.__init__(self)
        up.engines.mixins.OneshotPlannerMixin.__init__(self)
        self.horizon = horizon
        self.incremental = incremental
        self.solver_name = solver_name

    @staticmethod
    def _base_kind() -> ProblemKind:
        base_kind = ProblemKind()
        base_kind.set_problem_class("ACTION_BASED")
        base_kind.set_problem_type("SIMPLE_NUMERIC_PLANNING")
        base_kind.set_time("CONTINUOUS_TIME")
        base_kind.set_time("INTERMEDIATE_CONDITIONS_AND_EFFECTS")
        base_kind.set_time("TIMED_EFFECTS")
        base_kind.set_time("TIMED_GOALS")
        base_kind.set_time("DURATION_INEQUALITIES")
        base_kind.set_time("SELF_OVERLAPPING")
        base_kind.set_expression_duration("STATIC_FLUENTS_IN_DURATIONS")
        base_kind.set_expression_duration("FLUENTS_IN_DURATIONS")
        base_kind.set_expression_duration("INT_TYPE_DURATIONS")
        base_kind.set_expression_duration("REAL_TYPE_DURATIONS")
        base_kind.set_numbers("CONTINUOUS_NUMBERS")
        base_kind.set_numbers("DISCRETE_NUMBERS")
        base_kind.set_numbers("BOUNDED_TYPES")
        base_kind.set_conditions_kind("NEGATIVE_CONDITIONS")
        base_kind.set_conditions_kind("DISJUNCTIVE_CONDITIONS")
        base_kind.set_conditions_kind("EQUALITIES")
        base_kind.set_effects_kind("CONDITIONAL_EFFECTS")
        base_kind.set_effects_kind("INCREASE_EFFECTS")
        base_kind.set_effects_kind("DECREASE_EFFECTS")
        base_kind.set_effects_kind("STATIC_FLUENTS_IN_BOOLEAN_ASSIGNMENTS")
        base_kind.set_effects_kind("STATIC_FLUENTS_IN_NUMERIC_ASSIGNMENTS")
        base_kind.set_effects_kind("STATIC_FLUENTS_IN_OBJECT_ASSIGNMENTS")
        base_kind.set_effects_kind("FLUENTS_IN_BOOLEAN_ASSIGNMENTS")
        base_kind.set_effects_kind("FLUENTS_IN_NUMERIC_ASSIGNMENTS")
        base_kind.set_effects_kind("FLUENTS_IN_OBJECT_ASSIGNMENTS")
        base_kind.set_typing("FLAT_TYPING")
        base_kind.set_parameters("BOOL_FLUENT_PARAMETERS")
        base_kind.set_parameters("BOUNDED_INT_FLUENT_PARAMETERS")
        base_kind.set_parameters("BOOL_ACTION_PARAMETERS")
        base_kind.set_parameters("BOUNDED_INT_ACTION_PARAMETERS")
        base_kind.set_parameters("UNBOUNDED_INT_ACTION_PARAMETERS")
        base_kind.set_parameters("REAL_ACTION_PARAMETERS")
        base_kind.set_fluents_type("NUMERIC_FLUENTS")
        base_kind.set_fluents_type("INT_FLUENTS")
        base_kind.set_fluents_type("REAL_FLUENTS")
        base_kind.set_fluents_type("OBJECT_FLUENTS")
        return base_kind

    @staticmethod
    def get_credits(**kwargs) -> Optional["up.engines.Credits"]:
        return credits


class TempestEngine(_BaseEngine, up.engines.mixins.AnytimePlannerMixin):
    """Implementation of the TemPEST Engine."""

    @property
    def name(self) -> str:
        return "TemPEST"

    @staticmethod
    def supported_kind() -> ProblemKind:
        return _BaseEngine._base_kind()

    @staticmethod
    def supports(problem_kind: "up.model.ProblemKind") -> bool:
        return problem_kind <= TempestEngine.supported_kind()

    @staticmethod
    def satisfies(optimality_guarantee: "up.engines.OptimalityGuarantee") -> bool:
        return False

    @staticmethod
    def get_credits(**kwargs) -> Optional["up.engines.Credits"]:
        return credits

    def _solve(
        self,
        problem: "up.model.AbstractProblem",
        heuristic: Optional[Callable[["up.model.state.State"], Optional[float]]] = None,
        timeout: Optional[float] = None,
        output_stream: Optional[IO[str]] = None,
    ) -> "up.engines.results.PlanGenerationResult":
        assert isinstance(problem, up.model.Problem)
        if heuristic is not None:
            warnings.warn("TemPEST does not support custom heuristics.", UserWarning)

        return next(self._get_solutions_with_params(problem, timeout, output_stream))

    def _get_solutions_with_params(
        self,
        problem: "up.model.AbstractProblem",
        timeout: Optional[float] = None,
        output_stream: Optional[IO[str]] = None,
        warm_start_plan: Optional["up.plans.Plan"] = None,
        **kwargs,
    ) -> Iterator["up.engines.results.PlanGenerationResult"]:
        assert isinstance(problem, up.model.Problem)

        pysmt_env = pysmt.environment.Environment()

        modify_horizon = lambda x: x
        if self.incremental:
            encoder = IncrementalEncoder(problem, pysmt_env=pysmt_env, epsilon=problem.epsilon)
            modify_horizon = lambda x: x-1
        else:
            encoder = MonolithicEncoder(problem, pysmt_env=pysmt_env, epsilon=problem.epsilon)

        start_time = time()
        is_in_timeout: bool = False
        plan_found = False

        with pysmt_env.factory.Solver(name=self.solver_name, logic="QF_LRA") as smt:
            step_zero = encoder.encode_step_zero()
            if step_zero is not None:
                smt.add_assertion(step_zero)
            h = 2
            while self.horizon is None or h <= self.horizon:
                formula, assumptions = encoder.encode_step(modify_horizon(h))
                if formula is not None:
                    smt.add_assertion(formula)
                while smt.solve(assumptions):
                    model = smt.get_model()
                    plan = encoder.extract_plan(model, h)
                    res = PlanGenerationResult(
                        PlanGenerationResultStatus.SOLVED_SATISFICING,
                        plan,
                        self.name,
                    )
                    yield res
                    plan_found = True
                    elapsed_time = time() - start_time
                    if timeout is not None and elapsed_time > timeout:
                        is_in_timeout = True
                        break
                    l = []
                    for i in range(1, h):
                        for a in problem.actions:
                            if model.get_py_value(encoder.a(a, i)):
                                l.append(encoder.a(a, i))
                                for p in a.parameters:
                                    pv = model.get_py_value(encoder.symenc.parameter(a, p, i))
                                    l.append(encoder.mgr.EqualsOrIff(encoder.symenc.parameter(a, p, i), encoder.mgr.Real(pv)))
                            else:
                                l.append(encoder.mgr.Not(encoder.a(a, i)))
                    smt.add_assertion(encoder.mgr.Not(encoder.mgr.And(l)))
                if is_in_timeout:
                    break
                elapsed_time = time() - start_time
                if output_stream is not None:
                    output_stream.write(f"No solution with bound {h}. Elapsed_time: {elapsed_time:.3f} seconds\n")
                if timeout is not None and elapsed_time > timeout:
                    is_in_timeout = True
                    break
                h += 1

        if not plan_found:
            status = PlanGenerationResultStatus.TIMEOUT if is_in_timeout else PlanGenerationResultStatus.UNSOLVABLE_INCOMPLETELY
            yield PlanGenerationResult(status, None, self.name)

    def _get_solutions(
        self,
        problem: "up.model.AbstractProblem",
        timeout: Optional[float] = None,
        output_stream: Optional[IO[str]] = None,
    ) -> Iterator["up.engines.results.PlanGenerationResult"]:
        return self._get_solutions_with_params(problem, timeout, output_stream)


class TempestNonIncremental(TempestEngine):
    def __init__(self, horizon=None, solver_name=None):
        super().__init__(False, horizon, solver_name)


class TempestOptimal(_BaseEngine):
    """Implementation of the TemPEST Optimal Engine."""
    def __init__(self, incremental=True, horizon=None, solver_name=None, ground_abstract_step: bool = True, grounder_name: Optional[str] = None, sat_before_opt: bool = True, secondary_objective: Optional[str] = "weighted"):
        super().__init__(incremental, horizon, solver_name)
        self.ground_abstract_step = ground_abstract_step
        self.grounder_name = grounder_name
        self.sat_before_opt = sat_before_opt
        self.secondary_objective = secondary_objective

    @property
    def name(self) -> str:
        return "TemPEST Optimal"

    @staticmethod
    def supported_kind() -> ProblemKind:
        supported_kind = _BaseEngine._base_kind()
        supported_kind.set_quality_metrics("MAKESPAN")
        supported_kind.set_quality_metrics("ACTIONS_COST")
        supported_kind.set_actions_cost_kind("STATIC_FLUENTS_IN_ACTIONS_COST")
        supported_kind.set_actions_cost_kind("INT_NUMBERS_IN_ACTIONS_COST")
        supported_kind.set_actions_cost_kind("REAL_NUMBERS_IN_ACTIONS_COST")
        # These kind are removed due to the grounding of expressions checked to be True in the
        # last concrete step
        supported_kind.unset_parameters("UNBOUNDED_INT_ACTION_PARAMETERS")
        supported_kind.unset_parameters("REAL_ACTION_PARAMETERS")
        return supported_kind

    @staticmethod
    def supports(problem_kind: "up.model.ProblemKind") -> bool:
        return problem_kind <= TempestOptimal.supported_kind()

    @staticmethod
    def satisfies(optimality_guarantee: "up.engines.OptimalityGuarantee") -> bool:
        return True

    @staticmethod
    def get_credits(**kwargs) -> Optional["up.engines.Credits"]:
        return credits

    def _solve(
        self,
        problem: "up.model.AbstractProblem",
        heuristic: Optional[Callable[["up.model.state.State"], Optional[float]]] = None,
        timeout: Optional[float] = None,
        output_stream: Optional[IO[str]] = None,
    ) -> "up.engines.results.PlanGenerationResult":
        assert isinstance(problem, up.model.Problem)
        if heuristic is not None:
            warnings.warn("TemPEST does not support custom heuristics.", UserWarning)

        start_time = time()
        is_in_timeout: bool = False
        pysmt_env = pysmt.environment.Environment()

        epsilon = problem.epsilon
        if epsilon is None:
            epsilon = Fraction(1, 100)

        if self.sat_before_opt:
            # Find the first step where the problem has a plan using SMT
            # and then start using OMT from that step

            modify_horizon = lambda x: x
            if self.incremental:
                encoder = IncrementalEncoder(problem, pysmt_env=pysmt_env, epsilon=epsilon)
                modify_horizon = lambda x: x-1
            else:
                encoder = MonolithicEncoder(problem, pysmt_env=pysmt_env, epsilon=epsilon)

            h = 2
            first_sat_step = 0
            with pysmt_env.factory.Solver(name=self.solver_name, logic="QF_LRA") as smt:
                step_zero = encoder.encode_step_zero()
                if step_zero is not None:
                    smt.add_assertion(step_zero)
                while self.horizon is None or h <= self.horizon:
                    formula, assumptions = encoder.encode_step(modify_horizon(h))
                    if formula is not None:
                        smt.add_assertion(formula)
                    if smt.solve(assumptions):
                        first_sat_step = h
                        elapsed_time = time() - start_time
                        if output_stream is not None:
                            output_stream.write(f"SAT solution with bound {h}. Elapsed_time: {elapsed_time:.3f} seconds\n")
                    else:
                        elapsed_time = time() - start_time
                        if output_stream is not None:
                            output_stream.write(f"No SAT solution with bound {h}. Elapsed_time: {elapsed_time:.3f} seconds\n")
                        h += 1
                    if timeout is not None and elapsed_time > timeout:
                        is_in_timeout = True
                    if first_sat_step > 0 or is_in_timeout:
                        break

            if is_in_timeout:
                return PlanGenerationResult(
                    PlanGenerationResultStatus.TIMEOUT, None, self.name
                )
            if first_sat_step == 0:
                return PlanGenerationResult(
                    PlanGenerationResultStatus.UNSOLVABLE_INCOMPLETELY, None, self.name
                )
        else:
            # Start using OMT from first step
            first_sat_step = 2

        # Optimality part
        modify_horizon = lambda x: x
        if self.incremental:
            encoder = IncrementalEncoder(problem, pysmt_env=pysmt_env, epsilon=epsilon, optimal=True,
                ground_abstract_step=self.ground_abstract_step, grounder_name=self.grounder_name, secondary_objective=self.secondary_objective)
            modify_horizon = lambda x: x-1
        else:
            encoder = MonolithicEncoder(problem, pysmt_env=pysmt_env, epsilon=epsilon, optimal=True,
                ground_abstract_step=self.ground_abstract_step, grounder_name=self.grounder_name, secondary_objective=self.secondary_objective)

        h = 2
        with pysmt_env.factory.Optimizer(name=self.solver_name, logic="QF_LRA") as omt:
            step_zero = encoder.encode_step_zero()
            if step_zero is not None:
                omt.add_assertion(step_zero)

            if self.incremental:
                while h < first_sat_step:
                    formula, assumptions = encoder.encode_step(modify_horizon(h))
                    if formula is not None:
                        omt.add_assertion(formula)
                    omt.push()
                    h += 1
            else: # If there is no incrementality, all previous steps can be skipped
                h = first_sat_step

            while self.horizon is None or h <= self.horizon:
                formula, assumptions = encoder.encode_step(modify_horizon(h))
                if formula is not None:
                    omt.add_assertion(formula)
                omt.push()
                for a in assumptions:
                    omt.add_assertion(a)
                if self.incremental:
                    minimization_goals, extra_constraints = encoder.objective_to_minimize(modify_horizon(h), None)
                else:
                    minimization_goals, extra_constraints = encoder.objective_to_minimize(h-1, h)
                if extra_constraints is not None:
                    for ec in extra_constraints:
                        omt.add_assertion(ec)
                if self.secondary_objective is None or self.secondary_objective == "weighted":
                    assert len(minimization_goals) == 1
                    optimization_result = omt.optimize(minimization_goals[0])
                elif self.secondary_objective == "lexicographic":
                    optimization_result = omt.lexicographic_optimize(minimization_goals)
                else:
                    raise ValueError(f"Unknown secondary objective {self.secondary_objective}")
                if optimization_result is not None:
                    model, cost = optimization_result
                    if self.incremental:
                        uses_abstract_step = model.get_value(encoder.uses_abstact_step(modify_horizon(h), None)).is_true()
                    else:
                        uses_abstract_step = model.get_value(encoder.uses_abstact_step(h-1, h)).is_true()
                    if uses_abstract_step:
                        elapsed_time = time() - start_time
                        if output_stream is not None:
                            output_stream.write(f"Cost with bound {h}: {cost}. Elapsed_time: {elapsed_time:.3f} seconds\n")
                        h += 1
                        if timeout is not None and elapsed_time > timeout:
                            is_in_timeout = True
                            break
                    else:
                        if output_stream is not None:
                            output_stream.write(f"OPT solution with bound {h}: {cost}. Elapsed_time: {elapsed_time:.3f} seconds\n")
                        plan = encoder.extract_plan(model, h)
                        assert plan is not None
                        status = PlanGenerationResultStatus.SOLVED_OPTIMALLY if problem.quality_metrics  else PlanGenerationResultStatus.SOLVED_SATISFICING
                        res = PlanGenerationResult(
                            status,
                            plan,
                            self.name,
                        )
                        return res

                else:
                    # assert formula is None
                    break
                omt.pop()

        status = PlanGenerationResultStatus.TIMEOUT if is_in_timeout else PlanGenerationResultStatus.UNSOLVABLE_INCOMPLETELY

        return PlanGenerationResult(
            status, None, self.name
        )


class TempestOptimalNonIncremental(TempestOptimal):
    """Implementation of the TemPEST Optimal Engine."""
    def __init__(self, horizon=None, solver_name=None, ground_abstract_step: bool = True, grounder_name: Optional[str] = None, sat_before_opt: bool = True):
        super().__init__(False, horizon, solver_name, ground_abstract_step, grounder_name, sat_before_opt)


class TempestLiftedAbstractStep(TempestOptimal):
    def __init__(self, incremental=True, horizon=None, solver_name=None, sat_before_opt=True):
        super().__init__(incremental, horizon, solver_name, False, None, sat_before_opt)


class TempestOnlyOMT(TempestOptimal):
    def __init__(self, incremental=True, horizon=None, solver_name=None, ground_abstract_step=True, grounder_name=None):
        super().__init__(incremental, horizon, solver_name, ground_abstract_step, grounder_name, False)


class TempestLiftedAbstractStepOnlyOMT(TempestOptimal):
    def __init__(self, incremental=True, horizon=None, solver_name=None):
        super().__init__(incremental, horizon, solver_name, False, None, False)
