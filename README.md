# Mockup tempest README

## Requirements

- unified-planning
- pysmt, branch optimization

## Usage

After installing all the requirements and installing this tempest version you can use the `main.py` script can be used to dump the formulae. For additional info on the usage of the script you can do `python3 main.py -h`.

- The `--incremental` parameter activates or deactivates the usage of OMT solver incrementality; accepted values: `true`, `false`.
- The `--horizon` parameter is an integer >= 2 that gives an upper bound to the possible steps in the plan; it also specifies an upper bound to the dimension of the formula.
- The `--output-filename` parameter is optional and specifies a file path where the formulae are dumped instead of the stdout.

There are 2 ways to use the main script:

    - with pddl files
    - with a python package that generated the unified-planning Problem

### Generating the problem with PDDL files

To use the PDDL files it is sufficient to invoke the script with the `--pddl-domain` and `--pddl-problem` parameters, for example:

`python3 main.py --pddl-domain /home/user/mockup-tempest-benchmarks/benchmarks/pddl/Driverlog/action_costs/domain.pddl --pddl-problem /home/user/mockup-tempest-benchmarks/benchmarks/pddl/Driverlog/action_costs/instances/pfile1.pddl --incremental false --horizon 5`

### Generating the problem with a python package

To generate the problem with a python package, that package must be available in the PYTHONPATH; for example with the command: `export PYTHONPATH="/mockup-tempest-benchmarks/benchmarks/python:$PYTHONPATH"`

The parameters `--problem-package`, `--problem-function` and `--problem-params` must be specified to correctly generate the problem; for example:
`python3 main.py --problem-package Majsp --problem-function get_problems --problem-params "1, 1, 2, 1" --incremental true --horizon 7`

To find the correct problem parameters, there is an `instance.txt` file, where every line is a valid string of parameters.
