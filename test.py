import sys
from unified_planning.shortcuts import *
from unified_planning.test.examples import get_example_problems

from mockup import MockupOMTOptimizer

env = get_environment()
env.factory.add_engine("tempest-opt", "tempest.engine", "TempestOptimal")
env.credits_stream = None

pbs = get_example_problems()
problem = pbs["matchcellar"].problem
# print(problem)

with OneshotPlanner(name="tempest-opt", params={'incremental': True,
                                                'solver_name': 'MockupOMT',
                                                'sat_before_opt': False,
                                                'horizon': 10}) as p:
    res = p.solve(problem, output_stream=sys.stdout)
    print(res)

    if res.plan:
        with PlanValidator(problem_kind=problem.kind) as v:
            check = v.validate(problem, res.plan)
            print(check)
