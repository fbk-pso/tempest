# tempest

## tempest configuration parameters

Tempest has different parameters to configure the behaviour, some parameters are used by all Engines, while the majority of paramers is used only in the Optimal Engines.

The configuration parameters common to all engines are:

- **incremental**: a bool that determines if the algorithm used is incremental or monolithic. The incremental algorithm uses the incrementality of the solver among all the steps of the algorithm, while monolithic makes totally separated calls to the solver and it avoids caching of information from one call to another
- **horizon**: a positive integer that imposes an upper bound to the number of steps in the final plan. When set to None there is no limit to the step and the algorithm goes indefinitely, while with a fix horizon the algorithm stops when the step reaches the set horizon.
- **solver_name**: the name of the solver used by the pysmt solve call. In case of an Optimal Engine it must be the name of a pysmt Optimizer.

The configuration parameters specific to optimal engines are:

- **ground_abstract_step**: a bool that determines if the abstract step is grounded or lifted. When grounded the actions are instantiated on the objects, so more actions are created.
- **grounder_name**: a str representing the grounded installed in the unified_planning library that is used to ground the abstract step. When None the default in the preference list of the unified planning is used.
- **sat_before_opt**: a bool that determines if the optimal algorithm tries sat steps (which are faster) until it reaches a step that is sat before trying to find the optimal plan. When False the algorithm uses optimality at every step.
- **secondary objective**: a str with two possible values or None. When set to None there is no secondary objective to minimize, when set to *weighted* or *lexicographic* the algorithm minimizes the number of steps necessary to find the optimal plan.
