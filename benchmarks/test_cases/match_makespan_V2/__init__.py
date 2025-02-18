import os
from functools import partial

from utils import _get_pddl_test_cases
from test_cases.benchmarks_utils import add_optimum_to_test_cases

FILE_DIR = os.path.dirname(os.path.abspath(__file__))
PDDL_FILES_DIR = os.path.join(FILE_DIR, "pddl_files")

test_cases_optimal_values = {
    "match_makespan_v2_2_1": 70,
}

get_test_cases = partial(add_optimum_to_test_cases, partial(_get_pddl_test_cases, PDDL_FILES_DIR), test_cases_optimal_values)
