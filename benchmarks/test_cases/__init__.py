from functools import partial
try:
    # TODO find a cleaner way to do this
    from utils import _get_test_cases  # type: ignore

    get_test_cases = partial(_get_test_cases, "test_cases")
except Exception as e:
    pass
