# Copyright (C) 2025 PSO Unit, Fondazione Bruno Kessler
# This file is part of TemPEST.
#
# TemPEST is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# TemPEST is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program. If not, see <https://www.gnu.org/licenses/>.
#

import warnings
from collections.abc import Callable, Iterator
from fractions import Fraction
from time import time
from typing import IO, Any

import pysmt
import pysmt.environment
import unified_planning as up
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.logics import QF_LIRA, QF_LRA, QF_NIRA, QF_NRA, Logic
from pysmt.optimization.goal import MaxSMTGoal, MinimizationGoal
from pysmt.typing import BOOL
from unified_planning.engines import (
    Credits,
    PlanGenerationResult,
    PlanGenerationResultStatus,
)
from unified_planning.model import (
    DurativeAction,
    FNode,
    InstantaneousAction,
    ProblemKind,
)

from tempest.encoders import IncrementalEncoder, MonolithicEncoder
from tempest.encoders.base_encoder import BaseEncoder, _IrrationalModel

credits = Credits(
    "TemPEST",
    "FBK PSO Unit",
    "pso-tools@fbk.eu",
    "https://github.com/fbk-pso/tempest",
    "GPLv3",
    "Temporal Planning Encoding into Satisfiability Testing",
    "Temporal Planner that encodes temporal planning problems into SAT/SMT formulations",
)


def _expressions(problem: "up.model.Problem") -> Iterator[FNode]:
    for a in problem.actions:
        if isinstance(a, InstantaneousAction):
            yield from a.preconditions
            effects = a.effects
        else:
            assert isinstance(a, DurativeAction)
            yield a.duration.lower
            yield a.duration.upper
            for cs in a.conditions.values():
                yield from cs
            effects = [e for es in a.effects.values() for e in es]
        for e in effects:
            yield from (e.fluent, e.value, e.condition)
    yield from problem.goals
    for es in problem.timed_effects.values():
        for e in es:
            yield from (e.fluent, e.value, e.condition)
    for gs in problem.timed_goals.values():
        yield from gs


def _is_nonlinear(problem: "up.model.Problem") -> bool:
    static = problem.get_static_fluents()

    def varying(e: FNode) -> bool:
        # Static fluents encode to constants (or an ite over constants), never variables.
        if e.is_fluent_exp():
            return e.fluent() not in static
        if e.is_parameter_exp():
            t = e.parameter().type
            return t.is_int_type() or t.is_real_type()
        return any(varying(a) for a in e.args)

    # ponytail: tree walk without memoization, fine for planning-sized expressions
    def nonlinear(e: FNode) -> bool:
        if e.is_times() and sum(varying(a) for a in e.args) > 1:
            return True
        if e.is_div() and varying(e.arg(1)):
            return True
        return any(nonlinear(a) for a in e.args)

    return any(nonlinear(e) for e in _expressions(problem))


def _logic(problem: "up.model.Problem") -> Logic:
    # Only int action parameters are INT symbols; int fluents stay REAL.
    kind = problem.kind
    has_int = (
        kind.has_bounded_int_action_parameters()
        or kind.has_unbounded_int_action_parameters()
    )
    # No kind check: UP ignores products of parameters (p * p == 2 stays SIMPLE_NUMERIC).
    if _is_nonlinear(problem):
        return QF_NIRA if has_int else QF_NRA
    return QF_LIRA if has_int else QF_LRA


def _symbol_goal(omt: Any, goal: Any) -> Any:
    # PySMT's generic optimizers dispatch on the goal term's logic; ite(nonlinear goal, ...) reads as QF_NRA.
    mgr = omt.environment.formula_manager
    if isinstance(goal, MaxSMTGoal):
        res = MaxSMTGoal(real_weights=goal._real_weights)
        for clause, weight in goal.soft:
            b = mgr.FreshSymbol(BOOL, "soft%d")
            omt.add_assertion(mgr.Iff(b, clause))
            res.add_soft_clause(b, weight)
        return res
    assert isinstance(goal, MinimizationGoal)
    obj = mgr.FreshSymbol(omt.environment.stc.get_type(goal.term()), "objective%d")
    omt.add_assertion(mgr.Equals(obj, goal.term()))
    return MinimizationGoal(obj)


def _log_skip(output_stream: IO[str] | None, e: Exception, h: int) -> None:
    if output_stream is not None:
        reason = "irrational model" if isinstance(e, _IrrationalModel) else "unknown"
        output_stream.write(f"{reason} at bound {h}\n")


class _BaseEngine(up.engines.Engine, up.engines.mixins.OneshotPlannerMixin):
    """Implementation of the base tempest engine."""

    def __init__(
        self,
        incremental: bool = True,
        horizon: int | None = None,
        solver_name: str | None = None,
    ) -> None:
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
        base_kind.set_problem_type("GENERAL_NUMERIC_PLANNING")
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
        base_kind.set_parameters("REAL_ACTION_PARAMETERS")
        base_kind.set_parameters("BOUNDED_INT_ACTION_PARAMETERS")
        base_kind.set_parameters("UNBOUNDED_INT_ACTION_PARAMETERS")
        base_kind.set_fluents_type("NUMERIC_FLUENTS")
        base_kind.set_fluents_type("INT_FLUENTS")
        base_kind.set_fluents_type("REAL_FLUENTS")
        base_kind.set_fluents_type("OBJECT_FLUENTS")
        return base_kind

    @staticmethod
    def get_credits(**kwargs: Any) -> "up.engines.Credits | None":
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
    def get_credits(**kwargs: Any) -> "up.engines.Credits | None":
        return credits

    def _solve(
        self,
        problem: "up.model.AbstractProblem",
        heuristic: Callable[["up.model.state.State"], float | None] | None = None,
        timeout: float | None = None,
        output_stream: IO[str] | None = None,
    ) -> "up.engines.results.PlanGenerationResult":
        assert isinstance(problem, up.model.Problem)
        if heuristic is not None:
            warnings.warn(
                "TemPEST does not support custom heuristics.",
                UserWarning,
                stacklevel=2,
            )

        return next(self._get_solutions_with_params(problem, timeout, output_stream))

    def _get_solutions_with_params(
        self,
        problem: "up.model.AbstractProblem",
        timeout: float | None = None,
        output_stream: IO[str] | None = None,
        warm_start_plan: "up.plans.Plan | None" = None,
        **kwargs: Any,
    ) -> Iterator["up.engines.results.PlanGenerationResult"]:
        assert isinstance(problem, up.model.Problem)

        pysmt_env = pysmt.environment.Environment()

        modify_horizon = lambda x: x
        if self.incremental:
            encoder: BaseEncoder = IncrementalEncoder(
                problem, pysmt_env=pysmt_env, epsilon=problem.epsilon
            )
            modify_horizon = lambda x: x - 1
        else:
            encoder = MonolithicEncoder(
                problem, pysmt_env=pysmt_env, epsilon=problem.epsilon
            )

        start_time = time()
        is_in_timeout: bool = False
        plan_found = False

        with pysmt_env.factory.Solver(
            name=self.solver_name, logic=_logic(problem)
        ) as smt:
            step_zero = encoder.encode_step_zero()
            if step_zero is not None:
                smt.add_assertion(step_zero)
            h = 2
            while self.horizon is None or h <= self.horizon:
                formula, assumptions = encoder.encode_step(modify_horizon(h))
                if formula is not None:
                    smt.add_assertion(formula)
                try:
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
                        terms = []
                        for i in range(1, h):
                            for a in problem.actions:
                                if model.get_py_value(encoder.a(a, i)):
                                    terms.append(encoder.a(a, i))
                                    for p in a.parameters:
                                        pv = model.get_py_value(
                                            encoder.symenc.parameter(a, p, i)
                                        )
                                        terms.append(
                                            encoder.mgr.EqualsOrIff(
                                                encoder.symenc.parameter(a, p, i),
                                                encoder.mgr.Int(pv)
                                                if p.type.is_int_type()
                                                else encoder.mgr.Real(pv),
                                            )
                                        )
                                else:
                                    terms.append(encoder.mgr.Not(encoder.a(a, i)))
                        smt.add_assertion(encoder.mgr.Not(encoder.mgr.And(terms)))
                except (SolverReturnedUnknownResultError, _IrrationalModel) as e:
                    _log_skip(output_stream, e, h)
                if is_in_timeout:
                    break
                elapsed_time = time() - start_time
                if output_stream is not None:
                    output_stream.write(
                        f"No solution with bound {h}. Elapsed_time: {elapsed_time:.3f} seconds\n"
                    )
                if timeout is not None and elapsed_time > timeout:
                    is_in_timeout = True
                    break
                h += 1

        if not plan_found:
            status = (
                PlanGenerationResultStatus.TIMEOUT
                if is_in_timeout
                else PlanGenerationResultStatus.UNSOLVABLE_INCOMPLETELY
            )
            yield PlanGenerationResult(status, None, self.name)

    def _get_solutions(
        self,
        problem: "up.model.AbstractProblem",
        timeout: float | None = None,
        output_stream: IO[str] | None = None,
    ) -> Iterator["up.engines.results.PlanGenerationResult"]:
        return self._get_solutions_with_params(problem, timeout, output_stream)


class TempestNonIncremental(TempestEngine):
    def __init__(
        self, horizon: int | None = None, solver_name: str | None = None
    ) -> None:
        super().__init__(False, horizon, solver_name)


class TempestOptimal(_BaseEngine):
    """Implementation of the TemPEST Optimal Engine."""

    def __init__(
        self,
        incremental: bool = True,
        horizon: int | None = None,
        solver_name: str | None = None,
        ground_abstract_step: bool = True,
        grounder_name: str | None = None,
        sat_before_opt: bool = True,
        secondary_objective: str | None = "weighted",
    ) -> None:
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
        # This kind is removed due to the grounding of expressions checked to be True in the
        # last concrete step
        supported_kind.unset_parameters("REAL_ACTION_PARAMETERS")
        supported_kind.unset_parameters("UNBOUNDED_INT_ACTION_PARAMETERS")
        return supported_kind

    @staticmethod
    def supports(problem_kind: "up.model.ProblemKind") -> bool:
        return problem_kind <= TempestOptimal.supported_kind()

    @staticmethod
    def satisfies(optimality_guarantee: "up.engines.OptimalityGuarantee") -> bool:
        return True

    @staticmethod
    def get_credits(**kwargs: Any) -> "up.engines.Credits | None":
        return credits

    def _solve(
        self,
        problem: "up.model.AbstractProblem",
        heuristic: Callable[["up.model.state.State"], float | None] | None = None,
        timeout: float | None = None,
        output_stream: IO[str] | None = None,
    ) -> "up.engines.results.PlanGenerationResult":
        assert isinstance(problem, up.model.Problem)
        if heuristic is not None:
            warnings.warn(
                "TemPEST does not support custom heuristics.",
                UserWarning,
                stacklevel=2,
            )

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
                encoder: BaseEncoder = IncrementalEncoder(
                    problem, pysmt_env=pysmt_env, epsilon=epsilon
                )
                modify_horizon = lambda x: x - 1
            else:
                encoder = MonolithicEncoder(
                    problem, pysmt_env=pysmt_env, epsilon=epsilon
                )

            h = 2
            first_sat_step = 0
            with pysmt_env.factory.Solver(
                name=self.solver_name, logic=_logic(problem)
            ) as smt:
                step_zero = encoder.encode_step_zero()
                if step_zero is not None:
                    smt.add_assertion(step_zero)
                while self.horizon is None or h <= self.horizon:
                    formula, assumptions = encoder.encode_step(modify_horizon(h))
                    if formula is not None:
                        smt.add_assertion(formula)
                    try:
                        sat = smt.solve(assumptions)
                    except SolverReturnedUnknownResultError as e:
                        _log_skip(output_stream, e, h)
                        sat = False
                    if sat:
                        first_sat_step = h
                        elapsed_time = time() - start_time
                        if output_stream is not None:
                            output_stream.write(
                                f"SAT solution with bound {h}. Elapsed_time: {elapsed_time:.3f} seconds\n"
                            )
                    else:
                        elapsed_time = time() - start_time
                        if output_stream is not None:
                            output_stream.write(
                                f"No SAT solution with bound {h}. Elapsed_time: {elapsed_time:.3f} seconds\n"
                            )
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
            encoder: BaseEncoder = IncrementalEncoder(
                problem,
                pysmt_env=pysmt_env,
                epsilon=epsilon,
                optimal=True,
                ground_abstract_step=self.ground_abstract_step,
                grounder_name=self.grounder_name,
                secondary_objective=self.secondary_objective,
            )
            modify_horizon = lambda x: x - 1
        else:
            encoder = MonolithicEncoder(
                problem,
                pysmt_env=pysmt_env,
                epsilon=epsilon,
                optimal=True,
                ground_abstract_step=self.ground_abstract_step,
                grounder_name=self.grounder_name,
                secondary_objective=self.secondary_objective,
            )

        h = 2
        logic = _logic(problem)
        with pysmt_env.factory.Optimizer(name=self.solver_name, logic=logic) as omt:
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
            else:  # If there is no incrementality, all previous steps can be skipped
                h = first_sat_step

            while self.horizon is None or h <= self.horizon:
                formula, assumptions = encoder.encode_step(modify_horizon(h))
                if formula is not None:
                    omt.add_assertion(formula)
                omt.push()
                for a in assumptions:
                    omt.add_assertion(a)
                if self.incremental:
                    minimization_goals, extra_constraints = (
                        encoder.objective_to_minimize(modify_horizon(h), None)
                    )
                else:
                    minimization_goals, extra_constraints = (
                        encoder.objective_to_minimize(h - 1, h)
                    )
                if extra_constraints is not None:
                    for ec in extra_constraints:
                        omt.add_assertion(ec)
                if logic in (QF_NRA, QF_NIRA):
                    minimization_goals = [
                        _symbol_goal(omt, g) for g in minimization_goals
                    ]
                try:
                    if (
                        self.secondary_objective is None
                        or self.secondary_objective == "weighted"
                    ):
                        assert len(minimization_goals) == 1
                        optimization_result = omt.optimize(minimization_goals[0])
                    elif self.secondary_objective == "lexicographic":
                        optimization_result = omt.lexicographic_optimize(
                            minimization_goals
                        )
                    else:
                        raise ValueError(
                            f"Unknown secondary objective {self.secondary_objective}"
                        )
                    if optimization_result is not None:
                        model, cost = optimization_result
                        if self.incremental:
                            uses_abstract_step = model.get_value(
                                encoder.uses_abstact_step(modify_horizon(h), None)
                            ).is_true()
                        else:
                            uses_abstract_step = model.get_value(
                                encoder.uses_abstact_step(h - 1, h)
                            ).is_true()
                        if uses_abstract_step:
                            elapsed_time = time() - start_time
                            if output_stream is not None:
                                output_stream.write(
                                    f"Cost with bound {h}: {cost}. Elapsed_time: {elapsed_time:.3f} seconds\n"
                                )
                            h += 1
                            if timeout is not None and elapsed_time > timeout:
                                is_in_timeout = True
                                break
                        else:
                            if output_stream is not None:
                                output_stream.write(
                                    f"OPT solution with bound {h}: {cost}. Elapsed_time: {elapsed_time:.3f} seconds\n"
                                )
                            plan = encoder.extract_plan(model, h)
                            assert plan is not None
                            status = (
                                PlanGenerationResultStatus.SOLVED_OPTIMALLY
                                if problem.quality_metrics
                                else PlanGenerationResultStatus.SOLVED_SATISFICING
                            )
                            res = PlanGenerationResult(
                                status,
                                plan,
                                self.name,
                            )
                            return res

                    else:
                        # assert formula is None
                        break
                except (SolverReturnedUnknownResultError, _IrrationalModel) as e:
                    # ponytail: an irrational optimum recurs at every bound, so this runs to horizon/timeout
                    _log_skip(output_stream, e, h)
                    h += 1
                    if timeout is not None and time() - start_time > timeout:
                        is_in_timeout = True
                        break
                omt.pop()

        status = (
            PlanGenerationResultStatus.TIMEOUT
            if is_in_timeout
            else PlanGenerationResultStatus.UNSOLVABLE_INCOMPLETELY
        )

        return PlanGenerationResult(status, None, self.name)


class TempestOptimalNonIncremental(TempestOptimal):
    """Implementation of the TemPEST Optimal Engine."""

    def __init__(
        self,
        horizon: int | None = None,
        solver_name: str | None = None,
        ground_abstract_step: bool = True,
        grounder_name: str | None = None,
        sat_before_opt: bool = True,
    ) -> None:
        super().__init__(
            False,
            horizon,
            solver_name,
            ground_abstract_step,
            grounder_name,
            sat_before_opt,
        )


class TempestLiftedAbstractStep(TempestOptimal):
    def __init__(
        self,
        incremental: bool = True,
        horizon: int | None = None,
        solver_name: str | None = None,
        sat_before_opt: bool = True,
    ) -> None:
        super().__init__(incremental, horizon, solver_name, False, None, sat_before_opt)


class TempestOnlyOMT(TempestOptimal):
    def __init__(
        self,
        incremental: bool = True,
        horizon: int | None = None,
        solver_name: str | None = None,
        ground_abstract_step: bool = True,
        grounder_name: str | None = None,
    ) -> None:
        super().__init__(
            incremental,
            horizon,
            solver_name,
            ground_abstract_step,
            grounder_name,
            False,
        )


class TempestLiftedAbstractStepOnlyOMT(TempestOptimal):
    def __init__(
        self,
        incremental: bool = True,
        horizon: int | None = None,
        solver_name: str | None = None,
    ) -> None:
        super().__init__(incremental, horizon, solver_name, False, None, False)
