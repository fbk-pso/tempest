from fractions import Fraction
import os
from functools import partial

from utils import _get_pddl_test_cases
from test_cases.benchmarks_utils import add_optimum_to_test_cases

FILE_DIR = os.path.dirname(os.path.abspath(__file__))
PDDL_FILES_DIR = os.path.join(FILE_DIR, "pddl_files")

epsilon = Fraction(1, 100)
test_cases_optimal_values = {
    "p_simple_1": 1+epsilon, # In this case the optimum would be 1, but for a tempest incompletion it must be set to 1+epsilon
    "p_simple_2": Fraction(301, 100),
    "p_simple_3": 4,
}

get_test_cases = partial(add_optimum_to_test_cases, partial(_get_pddl_test_cases, PDDL_FILES_DIR), test_cases_optimal_values, epsilon)
