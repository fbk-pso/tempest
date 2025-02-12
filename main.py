#!/usr/bin/env python3

import argparse
import importlib

import unified_planning as up
from unified_planning.shortcuts import *
from unified_planning.io import PDDLReader

env = get_environment()
env.factory.add_engine("tempest-opt", "tempest.engine", "TempestOptimal")
env.credits_stream = None

set_credits_stream(None)


def convert_value(value):
    if value.lower() == 'true':
        return True
    elif value.lower() == 'false':
        return False
    try:
        return int(value)
    except ValueError:
        try:
            return float(value)
        except ValueError:
            return value


def get_python_problem(args):
    module = importlib.import_module(args.problem_package)
    problem_parameters = map(convert_value, args.problem_params.split(","))
    problem = getattr(module, args.problem_function)(*problem_parameters)
    return problem


def main():
    parser = argparse.ArgumentParser(description="Script to print the tempest formulae used to solve a planning problem. It allows 2 usages: 1 using pddl files, 1 using a python package that generates the problem.")
    parser.add_argument("--incremental", type=str, required=True, help="Defines if the formulation is incremental or monolithic; accepted values: true, false.")
    parser.add_argument("--output-filename", type=str, default=None, help="File path where the formulae are written. If omitted the formulas are written to stdout.")
    parser.add_argument("--horizon", type=int, required=True, help="Defines the number of steps written on the file/stdout.")
    parser.add_argument('--pddl-domain', type=str, help="The path to the pddl domain.")
    parser.add_argument('--pddl-problem', type=str, help="The path to the pddl problem.")
    parser.add_argument('--problem-package', type=str, help="The name of the python package that generates the unified_planning Problem to solve.")
    parser.add_argument('--problem-function', type=str, help="The name of the python function that generates the unified_planning Problem to solve.")
    parser.add_argument('--problem-params', type=str, help="The parameters passed to the python function. These must be a string of comma separated values, for example: \"1, 1, 2, 1\"")

    args = parser.parse_args()

    planner_name = "tempest-opt"

    if args.pddl_domain:
        assert args.pddl_problem is not None, "With a --pddl-domain also a --pddl-problem must be specified"
        assert args.problem_package is None and args.problem_function is None and args.problem_params is None, "When --pddl-domain and --pddl-problem are specified, --problem-package or --problem-function or --problem-params can't be specified"
        reader = PDDLReader()
        problem = reader.parse_problem(args.pddl_domain, args.pddl_problem)
    else:
        assert args.problem_package is not None and args.problem_function is not None and args.problem_params is not None, "When --pddl-domain is not specified, --problem-package and --problem-function and --problem-params must be specified"
        assert args.pddl_problem is None, "When --pddl-domain is not specified, --pddl-problem can't be specified"
        problem = get_python_problem(args)

    params = {
        'incremental': convert_value(args.incremental),
        'solver_name': 'MockupOMT',
        'sat_before_opt': False,
        'horizon': args.horizon,
    }
    assert isinstance(params["incremental"], bool), f"The incremental option must be true or false, found {params['incremental']}"

    if args.output_filename is None:
        with OneshotPlanner(name=planner_name, params=params) as planner:
            res = planner.solve(problem, output_stream=sys.stdout)
    else:
        with open(args.output_filename, "w") as output_stream:
            with OneshotPlanner(name=planner_name, params=params) as planner:
                res = planner.solve(problem, output_stream=output_stream)

if __name__ == '__main__':
    main()
