from fractions import Fraction
from typing import Callable, Dict, Union
from unified_planning.test import TestCase

def add_optimum_to_test_cases(get_test_cases: Callable[[], Dict[str, TestCase]], test_cases_optimal_values: Dict[str, Union[int, Fraction]], problem_epsilon = None):
    new_test_cases = {}
    for tc_name, tc in get_test_cases().items():
        tc_optimal_value = None
        for optimal_problem_name, optimal_value in test_cases_optimal_values.items():
            if optimal_problem_name in tc_name:
                tc_optimal_value = optimal_value
                break
        if tc_optimal_value is None:
            new_test_cases[tc_name] = tc
        else:
            tc.problem.epsilon = problem_epsilon
            new_test_cases[tc_name] = TestCase(
                problem = tc.problem,
                solvable = tc.solvable,
                optimum = tc_optimal_value,
                valid_plans = tc.valid_plans,
                invalid_plans = tc.invalid_plans
            )
    return new_test_cases
