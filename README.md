# TemPEST

**TemPEST** (Temporal Planner via Encoding into Satisfiability Testing) is a temporal planner that encodes temporal planning problems into SAT/SMT formulations, using modern SMT/OMT solvers to solve them efficiently.

TemPEST supports both **satisficing** and **optimal** temporal planning, with the ability to **minimize makespan** and **action costs**.

## Requirements

TemPEST relies on [PySMT](https://github.com/pysmt/pysmt) to interface with SMT/OMT solvers. You must install PySMT and at least one solver (e.g., Z3):

```bash
pip3 install pysmt>=0.9.7.dev333
pysmt-install --z3
```

## Installation

TemPEST is not currently available on PyPI and must be installed from source.

```bash
pip3 install git+https://github.com/fbk-pso/tempest.git
```

## Usage

TemPEST is fully integrated with the [Unified Planning](https://github.com/aiplan4eu/unified-planning) framework. You must register the planner engines with the Unified Planning environment:

```python
from unified_planning.shortcuts import *

# Register TemPEST engines
env = get_environment()
env.factory.add_engine("tempest", "tempest.engine", "TempestEngine")
env.factory.add_engine("tempest-opt", "tempest.engine", "TempestOptimal")

# Define your temporal planning problem
problem = ...

# Solve with TemPEST
with OneshotPlanner(name="tempest", params={'incremental': False}) as planner:
    result = planner.solve(problem)
    print(result.plan)
```

## Parameters

TemPEST has different parameters to configure its behavior. Some parameters are used by all engines, while most are specific to the optimal engines.

### Common to All Engines

- **`incremental`** (`bool`):
  Use incremental solver calls, reusing solver state across planning steps.
  `True` enables incremental solving; `False` makes separate, independent calls.

- **`horizon`** (`int | None`):
  Maximum number of steps in the final plan.
  If `None`, the search continues indefinitely.

- **`solver_name`** (`str`):
  The name of the SMT or OMT solver used by PySMT (e.g., `"z3"` or `"optimathsat"`).

### Specific to Optimal Engines

- **`ground_abstract_step`** (`bool`):
  Whether the abstract step is grounded (i.e., fully instantiated on objects).
  This typically increases the number of actions.

- **`grounder_name`** (`str | None`):
  The name of the grounder used from the `unified_planning` library.
  If `None`, the default grounder is selected.

- **`sat_before_opt`** (`bool`):
  Try satisficing steps before attempting optimization.
  `True` makes the planner search for feasible (SAT) plans before optimizing.

- **`secondary_objective`** (`str | None`):
  Guides the optimization beyond the main objective.
  Accepted values: `"weighted"`, `"lexicographic"`, or `None`.

## References

TemPEST is based on the following research papers:

- Panjkovic, S., & Micheli, A. (2024). *Abstract action scheduling for optimal temporal planning via OMT.* **AAAI 2024**

- Panjkovic, S., & Micheli, A. (2023). *Expressive optimal temporal planning via optimization modulo theory.* **AAAI 2023**

## License

TemPEST is released under the GNU Lesser General Public License v3.0 (LGPL-3.0).
See the `LICENSE` file for full details.

## Contact

For questions, bug reports, or contributions, please open an issue on GitHub or contact the authors.