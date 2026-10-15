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
from fractions import Fraction

import pytest
from pysmt.logics import QF_LIRA, QF_LRA
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

from tempest.engine import _logic

# Both bounds are non-integral, so the only integer in between is 2 while a
# real-valued solver is free to answer 1.5.
LOW, HIGH = Fraction(3, 2), Fraction(5, 2)


def _int_parameter_problem(durative: bool, bounded: bool = True) -> Problem:
    ptype = IntType(0, 10) if bounded else IntType()
    done = Fluent("done", BoolType())
    problem = Problem("int_parameter")
    problem.add_fluent(done, default_initial_value=False)
    if durative:
        da = DurativeAction("act", p=ptype)
        da.set_fixed_duration(1)
        da.add_condition(StartTiming(), GE(da.p, LOW))
        da.add_condition(StartTiming(), LE(da.p, HIGH))
        da.add_effect(EndTiming(), done, True)
        problem.add_action(da)
    else:
        ia = InstantaneousAction("act", p=ptype)
        ia.add_precondition(GE(ia.p, LOW))
        ia.add_precondition(LE(ia.p, HIGH))
        ia.add_effect(done, True)
        problem.add_action(ia)
    problem.add_goal(done)
    return problem


def _solve_and_check(problem: Problem, engine: str, incremental: bool) -> None:
    params = {"incremental": incremental, "solver_name": "z3"}
    # Fails on "We cannot establish whether TemPEST can solve this problem!".
    with warnings.catch_warnings():
        warnings.simplefilter("error")
        with OneshotPlanner(name=engine, params=params) as planner:
            res = planner.solve(problem)
    assert res.status in (
        PlanGenerationResultStatus.SOLVED_SATISFICING,
        PlanGenerationResultStatus.SOLVED_OPTIMALLY,
    )
    assert res.plan is not None
    with PlanValidator(problem_kind=problem.kind) as validator:
        assert validator.validate(problem, res.plan)
    plan = res.plan
    if isinstance(plan, TimeTriggeredPlan):
        (ai,) = [ai for _, ai, _ in plan.timed_actions]
    else:
        assert isinstance(plan, SequentialPlan)
        (ai,) = plan.actions
    value = ai.actual_parameters[0]
    assert value.is_int_constant()
    assert value.int_constant_value() == 2


@pytest.mark.parametrize("incremental", [True, False])
@pytest.mark.parametrize("durative", [False, True])
def test_int_parameter_is_integral(incremental: bool, durative: bool) -> None:
    _solve_and_check(_int_parameter_problem(durative), "tempest", incremental)


def test_unbounded_int_parameter() -> None:
    problem = _int_parameter_problem(durative=True, bounded=False)
    _solve_and_check(problem, "tempest", incremental=True)


def test_int_parameter_optimal() -> None:
    _solve_and_check(_int_parameter_problem(durative=True), "tempest-opt", True)


def test_logic_only_for_int_parameters() -> None:
    assert _logic(_int_parameter_problem(durative=True)) == QF_LIRA
    # An int fluent alone keeps QF_LRA: it is integral by induction on its effects.
    problem = Problem("int_fluent")
    counter = Fluent("counter", IntType(0, 10))
    problem.add_fluent(counter, default_initial_value=0)
    ia = InstantaneousAction("inc")
    ia.add_increase_effect(counter, 1)
    problem.add_action(ia)
    problem.add_goal(GE(counter, 2))
    assert _logic(problem) == QF_LRA
