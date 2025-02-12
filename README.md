# tempest-mockup

This repo has a tempest-mockup that dumps the formulae used to solve a planning problem either to a file or to stdout.

## Requirements

- unified-planning
- pysmt, branch optimization
- some benchmarks, either in pddl format or with a python function that generated the unified-planning Problem

## Usage

After installing all the requirements and installing this tempest version you can use the `main.py` script can be used to dump the formulae. For additional info on the usage of the script you can do `python3 main.py -h`.

The `--incremental` and `--horizon` parameters are required, the `--output-filename` parameter can be specified to dump the output in a file instead of in the stdout, the problem can be generated in 2 different ways:

    - with pddl files
    - with a python package that generated the unified-planning Problem

### Generating the problem with PDDL files

To use the PDDL files it is sufficient to invoke the script with the `--pddl-domain` and `--pddl-problem` parameters, for example:

`python3 main.py --pddl-domain path/to/domain.pddl --pddl-problem path/to/problem.pddl --output-filename path/to/out.txt --incremental false --horizon 5`

### Generating the problem with a python package

To generate the problem with a python package, that package must be available in the PYTHONPATH; for example with the command: `export PYTHONPATH="/home/user/path/to/benchmarks/:$PYTHONPATH"`

The parameters `--problem-package`, `--problem-function` and `--problem-params` must be specified to correctly generate the problem; for example:
`python3 main.py --problem-package other_benchmarks.Majsp --problem-function get_problems --problem-params "1, 1, 2, 1" --output-filename "./out_majsp.txt" --incremental true --horizon 5`
