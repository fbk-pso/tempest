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

import io
import warnings

import pytest
from pysmt.logics import QF_LRA, QF_NIRA, QF_NRA
from unified_planning.engines import PlanGenerationResultStatus
from unified_planning.model import Fluent
from unified_planning.model.metrics import MinimizeActionCosts
from unified_planning.plans import SequentialPlan, TimeTriggeredPlan
from unified_planning.shortcuts import (
    GE,
    BoolType,
    DurativeAction,
    EndTiming,
    Equals,
    InstantaneousAction,
    IntType,
    OneshotPlanner,
    PlanValidator,
    Problem,
    RealType,
    StartTiming,
    Times,
)

from tempest.engine import _logic


def _square_problem(durative: bool, nonlinear_goal: bool = False) -> Problem:
    # From x = 2, reaching x >= 16 takes exactly two applications of x := x * x.
    x = Fluent("x", RealType())
    problem = Problem("square")
    problem.add_fluent(x, default_initial_value=2)
    if durative:
        da = DurativeAction("square")
        da.set_fixed_duration(1)
        da.add_condition(StartTiming(), GE(x, 0))
        da.add_effect(EndTiming(), x, Times(x, x))
        problem.add_action(da)
    else:
        ia = InstantaneousAction("square")
        ia.add_effect(x, Times(x, x))
        problem.add_action(ia)
    problem.add_goal(GE(Times(x, x), 256) if nonlinear_goal else GE(x, 16))
    return problem


def test_logic_from_nonlinearity() -> None:
    assert _logic(_square_problem(durative=False)) == QF_NRA

    problem = _square_problem(durative=False)
    scale = InstantaneousAction("scale", p=IntType(1, 3))
    scale.add_effect(problem.fluent("x"), Times(problem.fluent("x"), scale.p))
    problem.add_action(scale)
    assert _logic(problem) == QF_NIRA

    # Robot-style: UP calls these general numeric, but they encode linearly.
    problem = Problem("linear_general")
    x = Fluent("x", RealType())
    y = Fluent("y", RealType())
    k = Fluent("k", RealType())
    problem.add_fluent(x, default_initial_value=0)
    problem.add_fluent(y, default_initial_value=5)
    problem.add_fluent(k, default_initial_value=3)
    a = InstantaneousAction("move")
    a.add_effect(x, y - 1)
    a.add_effect(y, Times(y, k) / 2)
    problem.add_action(a)
    problem.add_goal(GE(x, 4))
    assert problem.kind.has_general_numeric_planning()
    assert _logic(problem) == QF_LRA


@pytest.mark.parametrize("nonlinear_goal", [False, True])
@pytest.mark.parametrize("durative", [False, True])
@pytest.mark.parametrize("engine", ["tempest", "tempest-opt"])
def test_square(engine: str, durative: bool, nonlinear_goal: bool) -> None:
    # A nonlinear goal makes the OMT objective ite(goal, ...) nonlinear too.
    problem = _square_problem(durative, nonlinear_goal)
    if engine == "tempest-opt":
        problem.add_quality_metric(MinimizeActionCosts({problem.action("square"): 1}))
    # Only TemPEST's own warning is fatal; pysmt warns about real objectives.
    with warnings.catch_warnings():
        warnings.filterwarnings("error", message="We cannot establish")
        with OneshotPlanner(name=engine) as planner:
            res = planner.solve(problem)
    assert res.status in (
        PlanGenerationResultStatus.SOLVED_SATISFICING,
        PlanGenerationResultStatus.SOLVED_OPTIMALLY,
    )
    assert res.plan is not None
    with PlanValidator(problem_kind=problem.kind) as validator:
        assert validator.validate(problem, res.plan)
    if engine == "tempest-opt":
        plan = res.plan
        if isinstance(plan, TimeTriggeredPlan):
            assert len(plan.timed_actions) == 2
        else:
            assert isinstance(plan, SequentialPlan)
            assert len(plan.actions) == 2


def test_irrational_model_is_skipped() -> None:
    # The only plans need p = sqrt(2), which a UP plan cannot represent.
    done = Fluent("done", BoolType())
    problem = Problem("irrational")
    problem.add_fluent(done, default_initial_value=False)
    a = InstantaneousAction("pick", p=RealType(0, 10))
    a.add_precondition(Equals(Times(a.p, a.p), 2))
    a.add_effect(done, True)
    problem.add_action(a)
    problem.add_goal(done)
    assert _logic(problem) == QF_NRA

    out = io.StringIO()
    with OneshotPlanner(name="tempest", params={"horizon": 3}) as planner:
        res = planner.solve(problem, output_stream=out)
    assert res.status == PlanGenerationResultStatus.UNSOLVABLE_INCOMPLETELY
    assert "irrational model at bound" in out.getvalue()
