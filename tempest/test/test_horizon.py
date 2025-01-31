# Copyright 2021-2023 AIPlan4EU project
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


from typing import Iterator, Tuple
from unittest import TestCase
from unified_planning.shortcuts import *

class TestHorizon(TestCase):
    def test_horizon(self):

        engines_and_params = [
            ("tempest", {"incremental": True}),
            ("tempest", {"incremental": False}),
            ("tempest-opt", {"incremental": True, "sat_before_opt": True, "ground_abstract_step": True}),
            ("tempest-opt", {"incremental": False, "sat_before_opt": True, "ground_abstract_step": True}),
            ("tempest-opt", {"incremental": True, "sat_before_opt": False, "ground_abstract_step": True}),
            ("tempest-opt", {"incremental": False, "sat_before_opt": False, "ground_abstract_step": True}),
            ("tempest-opt", {"incremental": True, "sat_before_opt": True, "ground_abstract_step": False}),
            ("tempest-opt", {"incremental": False, "sat_before_opt": True, "ground_abstract_step": False}),
            ("tempest-opt", {"incremental": True, "sat_before_opt": False, "ground_abstract_step": False}),
            ("tempest-opt", {"incremental": False, "sat_before_opt": False, "ground_abstract_step": False}),
        ]

        for problem, min_correct_horizon in self._get_problems_with_min_horizon():
            for engine, params in engines_and_params:
                # prove that the plan is never found with horizon = min_correct_horizon -1
                # and that it is found with horizon = min_correct_horizon
                # (if optimal, the min_correct_horizon is set to +inf)
                params["horizon"] = min_correct_horizon-1
                with OneshotPlanner(name=engine, params=params) as planner:
                    result = planner.solve(problem)
                    self.assertIsNone(result.plan, f"{problem.name}, {min_correct_horizon}, {params}")

                params["horizon"] = min_correct_horizon if "opt" not in engine else None

                # Set for tests efficiency
                if "opt" in engine and min_correct_horizon >= 3:
                    continue

                with OneshotPlanner(name=engine, params=params) as planner:
                    result = planner.solve(problem, output_stream = sys.stdout)
                    self.assertIsNotNone(result.plan,  f"{problem.name}, {min_correct_horizon}, {params}")

    def _get_problems_with_min_horizon(self) -> Iterator[Tuple[Problem, int]]:
        for problem, min_correct_horizon in self._basic_counter():
            yield problem, min_correct_horizon
        for problem, min_correct_horizon in self._move_ball():
            yield problem, min_correct_horizon

    def _basic_counter(self) -> Iterator[Tuple[Problem, int]]:
        base_problem = Problem("counter")
        counter = base_problem.add_fluent("counter", IntType(), default_initial_value=0)

        increase_counter = DurativeAction("increase counter")
        increase_counter.set_fixed_duration(1)
        increase_counter.add_increase_effect(EndTiming(), counter, 1)

        base_problem.add_action(increase_counter)

        for i in range(1, 6):
            problem = base_problem.clone()
            problem.add_goal(Equals(counter, i))
            # 2 steps to start and end the plan
            # 1 step for every action because only the step to end the action is added;
            # the action starts when the previous ends so no additional step is needed
            min_correct_horizon = 2+i
            yield problem, min_correct_horizon

        base_problem.name = "counter-intermediate-effect"
        base_problem.clear_actions()

        increase_counter = DurativeAction("increase counter")
        increase_counter.set_fixed_duration(1)
        increase_counter.add_increase_effect(
            StartTiming(Fraction(1, 2)),
            counter,
            1
        )

        base_problem.add_action(increase_counter)

        for i in range(1, 4):
            problem = base_problem.clone()
            problem.add_goal(Equals(counter, i))
            # 2 steps to start and end the plan
            # 2 step for every action because the step to end the action and
            # the step to do the intermediate effect are added
            # the action starts when the previous ends so no additional step is needed
            min_correct_horizon = 2+2*i
            yield problem, min_correct_horizon

        base_problem.name = "counter-intermediate-effect-condition"
        base_problem.clear_actions()

        increase_counter = DurativeAction("increase counter")
        increase_counter.set_fixed_duration(1)
        increase_counter.add_condition(
            StartTiming(Fraction(1, 2)),
            counter >= 0,
        )
        increase_counter.add_increase_effect(
            StartTiming(Fraction(2, 3)),
            counter,
            1
        )

        base_problem.add_action(increase_counter)

        for i in range(1, 4):
            problem = base_problem.clone()
            problem.add_goal(Equals(counter, i))
            # 2 steps to start and end the plan
            # 2 step for every action because the step to end the action and
            # the step to do the intermediate effect are added
            # no additional step for the condition is added
            # the action starts when the previous ends so no additional step is needed
            min_correct_horizon = 2+2*i
            yield problem, min_correct_horizon

    def _move_ball(self):
        base_problem = Problem("move ball")
        Ball = UserType("Ball")
        Location = UserType("Location")

        l1, l2, l3 = (base_problem.add_object(f"l{i}", Location) for i in range(1, 4))
        b1, b2, b3 = (base_problem.add_object(f"b{i}", Ball) for i in range(1, 4))

        robot_loaded = base_problem.add_fluent("robot_loaded", BoolType(), default_initial_value=False)
        ball_on_robot = base_problem.add_fluent("ball_on_robot", Ball, default_initial_value=b1)
        robot_at = base_problem.add_fluent("robot_at", Location, default_initial_value=l1)
        ball_at = base_problem.add_fluent("ball_at", Location, default_initial_value=l1, ball=Ball)

        pick = InstantaneousAction("pick", ball=Ball, l_from=Location)
        pick.add_precondition(Not(robot_loaded))
        pick.add_precondition(robot_at.Equals(pick.l_from))
        pick.add_precondition(ball_at(pick.ball).Equals(pick.l_from))

        pick.add_effect(robot_loaded, True)
        pick.add_effect(ball_on_robot, pick.ball)

        drop = InstantaneousAction("drop", ball=Ball, l_to=Location)
        drop.add_precondition(robot_loaded())
        drop.add_precondition(ball_on_robot.Equals(drop.ball))
        drop.add_precondition(robot_at.Equals(drop.l_to))

        drop.add_effect(robot_loaded, False)
        drop.add_effect(ball_at(drop.ball), drop.l_to)

        move = DurativeAction("move", l_from=Location, l_to=Location)
        move.set_fixed_duration(Int(5))
        move.add_condition(StartTiming(), robot_at.Equals(move.l_from))

        move.add_effect(EndTiming(), robot_at, move.l_to)

        base_problem.add_actions([pick, drop, move])

        problem = base_problem.clone()
        problem.add_goal(ball_at(b2).Equals(l2))
        min_correct_horizon = 4
        yield problem, min_correct_horizon

        problem = base_problem.clone()
        problem.add_goal(ball_at(b2).Equals(l2))
        problem.add_goal(ball_at(b3).Equals(l3))
        min_correct_horizon = 8
        yield problem, min_correct_horizon
