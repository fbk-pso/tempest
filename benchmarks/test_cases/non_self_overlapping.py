from unified_planning.shortcuts import *
from unified_planning.test import TestCase

# short description:
# this domain has a global counter (counter fluent) that needs an object of type
# CounterElement in order to increase
# The action takes 5 seconds, after that the counter is freed. With N objects of
# type CounterElement the counter can be increased max N times n 5 seconds, due to
# the non self-overlapping features.
# Using timed goals it is possible to test the non self-overlapping feature of an engine

ACTION_DURATION = 5

#Setting up Types
CounterElement = UserType("CounterElement")

#Setting up Fluents
counter = Fluent("counter", IntType())

#Setting up Actions:
increase_counter = DurativeAction("increase_counter", p=CounterElement)
increase_counter.set_fixed_duration(ACTION_DURATION)
increase_counter.add_increase_effect(EndTiming(), counter, 1)

#Setting up the number of CounterElement object, the goal value for the counter and after how many seconds that goal must be reached

ALL_PARAMS = [
    # nCounterElements, goal_value, goal_time
    (1, 1, 5.1),
    (1, 2, 5.1),
    (1, 2, 10.1),
    (2, 2, 5),
    (3, 3, 5.1),
]

def _get_problem(problem_id, nCounterElements, goal_value, goal_time):

    p = Problem(f"non_self_overlapping_{problem_id}")
    p.add_fluent(counter, default_initial_value=0)
    p.add_action(increase_counter)

    p.add_objects((Object(f"ce_{i}",CounterElement) for i in range(nCounterElements)))

    p.add_timed_goal(
        TimePointInterval(GlobalStartTiming(Fraction(goal_time))),
        Equals(counter, goal_value)
    )

    max_action_repetitions = int(goal_time/ACTION_DURATION)
    max_counter_value = max_action_repetitions * nCounterElements
    is_solvable = max_counter_value > goal_value or (max_counter_value == goal_value and goal_time/ACTION_DURATION > max_action_repetitions)

    return p, is_solvable

def get_test_cases():
    problems = {f"non_self_overlapping_{i}": TestCase(*_get_problem(i, *params)) for i, params in enumerate(ALL_PARAMS)}
    return problems

def get_problem(nCounterElements=2, goal_value=2, goal_time=5.1):
    return _get_problem(0, nCounterElements, goal_value, goal_time)[0]
