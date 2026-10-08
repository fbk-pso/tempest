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

from fractions import Fraction

import pytest
from unified_planning.engines import PlanGenerationResultStatus
from unified_planning.model import Fluent
from unified_planning.plans import SequentialPlan, TimeTriggeredPlan
from unified_planning.shortcuts import (
    GE,
    LE,
    BoolType,
    DurativeAction,
    EndTiming,
    InstantaneousAction,
    IntType,
    OneshotPlanner,
    PlanValidator,
    Problem,
    StartTiming,
)

# Both bounds are non-integral, so the only integer in between is 2 while a
# real-valued solver is free to answer 1.5.
LOW, HIGH = Fraction(3, 2), Fraction(5, 2)


def _int_parameter_problem(durative: bool) -> Problem:
    done = Fluent("done", BoolType())
    problem = Problem("int_parameter")
    problem.add_fluent(done, default_initial_value=False)
    if durative:
        da = DurativeAction("act", p=IntType(0, 10))
        da.set_fixed_duration(1)
        da.add_condition(StartTiming(), GE(da.p, LOW))
        da.add_condition(StartTiming(), LE(da.p, HIGH))
        da.add_effect(EndTiming(), done, True)
        problem.add_action(da)
    else:
        ia = InstantaneousAction("act", p=IntType(0, 10))
        ia.add_precondition(GE(ia.p, LOW))
        ia.add_precondition(LE(ia.p, HIGH))
        ia.add_effect(done, True)
        problem.add_action(ia)
    problem.add_goal(done)
    return problem


def _solve(problem: Problem, incremental: bool) -> SequentialPlan | TimeTriggeredPlan:
    params = {"incremental": incremental, "solver_name": "z3"}
    with OneshotPlanner(name="tempest", params=params) as planner:
        res = planner.solve(problem)
    assert res.status == PlanGenerationResultStatus.SOLVED_SATISFICING
    assert res.plan is not None
    with PlanValidator(problem_kind=problem.kind) as validator:
        assert validator.validate(problem, res.plan)
    assert isinstance(res.plan, (SequentialPlan, TimeTriggeredPlan))
    return res.plan


def _action_instances(plan: SequentialPlan | TimeTriggeredPlan) -> list:
    if isinstance(plan, TimeTriggeredPlan):
        return [ai for _, ai, _ in plan.timed_actions]
    return plan.actions


@pytest.mark.parametrize("incremental", [True, False])
@pytest.mark.parametrize("durative", [False, True])
def test_int_parameter_is_integral(incremental: bool, durative: bool) -> None:
    plan = _solve(_int_parameter_problem(durative), incremental)
    (ai,) = _action_instances(plan)
    value = ai.actual_parameters[0]
    assert value.is_int_constant()
    assert value.int_constant_value() == 2
