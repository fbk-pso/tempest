from time import time
import pysmt
import warnings
import unified_planning as up

from unified_planning.model import ProblemKind
from unified_planning.engines import (
    PlanGenerationResultStatus,
    PlanGenerationResult,
    Credits,
)
from unified_planning.engines.results import correct_plan_generation_result
from unified_planning.plans import TimeTriggeredPlan
from typing import IO, Callable, Optional
from pysmt.shortcuts import Solver
from tempest.encoders import MonolithicEncoder, IncrementalEncoder


credits = Credits(
    "TemPEST",
    "FBK PSO Unit",
    "tamer@fbk.eu",
    "https://tamer.fbk.eu",
    "Free for Educational Use",
    "Temporal Planning Encoding into Satisfiability Testing",
    "Temporal Planning Encoding into Satisfiability Testing",
)


class BaseEngine(up.engines.Engine, up.engines.mixins.OneshotPlannerMixin):
    """Implementation of the base tempest engine."""

    def __init__(self, incremental=True, horizon=None):
        up.engines.Engine.__init__(self)
        up.engines.mixins.OneshotPlannerMixin.__init__(self)
        self.horizon = horizon
        self.incremental = incremental

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
        base_kind.set_fluents_type("OBJECT_FLUENTS")
        return base_kind

    @staticmethod
    def get_credits(**kwargs) -> Optional["up.engines.Credits"]:
        return credits

class TempestEngine(BaseEngine):
    """Implementation of the TemPEST Engine."""

    @property
    def name(self) -> str:
        return "TemPEST"

    @staticmethod
    def supported_kind() -> ProblemKind:
        return BaseEngine._base_kind()

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

        pysmt_env = pysmt.environment.Environment()

        modify_horizon = lambda x: x
        if self.incremental:
            encoder = IncrementalEncoder(problem, pysmt_env=pysmt_env)
            modify_horizon = lambda x: x-1
        else:
            encoder = MonolithicEncoder(problem, pysmt_env=pysmt_env)

        start_time = time()
        is_in_timeout: bool = False

        with Solver(logic="QF_NRA") as smt:
            step_zero = encoder.encode_step_zero()
            if step_zero is not None:
                smt.add_assertion(step_zero)
            h = 2
            while self.horizon is None or h <= self.horizon:
                formula, assumptions = encoder.encode_step(modify_horizon(h))
                if formula is not None:
                    smt.add_assertion(formula)
                if smt.solve(assumptions):
                    plan = encoder.extract_plan(smt.get_model(), h)
                    res = PlanGenerationResult(
                        PlanGenerationResultStatus.SOLVED_SATISFICING,
                        plan,
                        self.name,
                    )
                    if isinstance(plan, TimeTriggeredPlan):
                        return correct_plan_generation_result(res, problem, None)
                    else:
                        return res
                else:
                    elapsed_time = time() - start_time
                    if output_stream is not None:
                        output_stream.write(f"No solution with bound {h}. Elapsed_time: {elapsed_time:.3f} seconds\n")
                    h += 1
                    if timeout is not None and elapsed_time > timeout:
                        is_in_timeout = True
                        break

        status = PlanGenerationResultStatus.TIMEOUT if is_in_timeout else PlanGenerationResultStatus.UNSOLVABLE_INCOMPLETELY

        return PlanGenerationResult(
            status, None, self.name
        )
