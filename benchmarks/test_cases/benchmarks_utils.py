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
