# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Quick orientation

TemPEST (Temporal Planner via Encoding into Satisfiability Testing) is a
temporal planner that encodes temporal planning problems into SAT/SMT/OMT and
solves them with [PySMT](https://github.com/pysmt/pysmt)-backed solvers
([README.md](README.md)). It is a pure-Python package.

It ships one PyPI wheel: the distribution name is **`up-tempest`** (the name
`tempest` was taken on PyPI), while the **import package is `tempest`**
(source under `src/tempest/`). It integrates with
[Unified Planning](https://github.com/aiplan4eu/unified-planning) (UP) as a set
of planner engines.

## Repository layout

```
/
├── pyproject.toml              # up-tempest (hatchling); uv project root
├── uv.lock                     # committed; pins all Python deps incl. unified-planning git rev
├── src/tempest/                # Python package (PEP-660 src layout)
│   ├── engine.py               # UP engine classes (TempestEngine, TempestOptimal, ...)
│   ├── converter.py            # UP expression -> PySMT (DagWalker)
│   └── encoders/               # SAT/SMT/OMT problem encoders
├── tests/                      # pytest suite (outside src/, modern best practice)
├── benchmarks/                 # UP problem definitions + PDDL files used by tests & CI report
├── doc/tempest_demo.ipynb      # runnable demo notebook
├── ci/stamp_dev_version.py     # dev-version stamper for main builds
├── justfile                    # task runner — single source of truth for dev + CI commands
├── .pre-commit-config.yaml
└── .github/workflows/
    ├── test.yml                # reusable: lint + test
    ├── test_specific_engine.yml # reusable: one UP report per engine variant
    ├── ci-pr.yml               # PR trigger (test.yml + the 7-engine report matrix)
    └── build-and-release.yml   # main + tag trigger; builds, publishes, releases
```

## Setup

```bash
uv sync                      # .venv + dev deps (z3 is a mandatory dependency)
uv run pre-commit install    # one-time
# Optional: OptiMathSAT for the full test suite (compiled into the venv):
uv pip install setuptools
uv run --no-sync pysmt-install --optimsat --confirm-agreement
```

`uv` is required. `just` is the task runner — install via `uv tool install rust-just` or your package manager.

## Common tasks (all via `just`)

| Recipe | What it does |
|---|---|
| `just install` | `uv sync` |
| `just test` | `uv run pytest tests/ -v` |
| `just lint` | Ruff check + format --check over `src tests ci` |
| `just format` | Ruff format + ruff check --fix over `src tests ci` |
| `just typecheck` | `uv run mypy` (config in `pyproject.toml`, scope `src/tempest`) |
| `just precommit` | `pre-commit run --all-files --show-diff-on-failure` — same as CI's `lint` job |
| `just build` | `uv build` — produce the `up-tempest` sdist + wheel into `./dist/` |
| `just bump VERSION` | Update version in `pyproject.toml` + refresh `uv.lock` |
| `just clean` | Remove build/dist/cache dirs |

## Running the test suite

Tests need `unified-planning` (installed by `uv sync` from its upstream `main`,
the exact commit pinned in `uv.lock`) and SMT/OMT solvers. [tests/test_horizon.py](tests/test_horizon.py) exercises
both `z3` (a mandatory dependency, always present) and `optimsat` (installed via
`pysmt-install`):

```bash
uv sync
uv pip install setuptools  # build-time only, for pysmt-install
uv run --no-sync pysmt-install --optimsat --confirm-agreement
just test
```

Engine registration for the tests happens in [tests/conftest.py](tests/conftest.py)
(it calls `up_env.factory.add_engine(...)` at collection time). Benchmark
problems in [benchmarks/](benchmarks/) are added to `sys.path` by the test
modules themselves.

## Architecture

### Engine ([src/tempest/engine.py](src/tempest/engine.py))

`_BaseEngine` implements UP's `OneshotPlannerMixin`. Concrete engines:

- `TempestEngine` (also `AnytimePlannerMixin`) — satisficing.
- `TempestNonIncremental` — same, non-incremental solver calls.
- `TempestOptimal` and its variants (`TempestOptimalNonIncremental`,
  `TempestLiftedAbstractStep`, `TempestOnlyOMT`,
  `TempestLiftedAbstractStepOnlyOMT`) — optimal planning via OMT.

Engines are exposed to UP under the names `tempest`, `tempest-ni`,
`tempest-opt`, `tempest-opt-ni`, `tempest-las`, `tempest-oomt`,
`tempest-las-oomt` (see [ci-pr.yml](.github/workflows/ci-pr.yml) and
[tests/conftest.py](tests/conftest.py)).

### Encoders ([src/tempest/encoders/](src/tempest/encoders/))

`BaseEncoder` (ABC in `base_encoder.py`) builds the SMT/OMT encoding of a
grounded UP `Problem` at a given horizon. Concrete encoders:
`MonolithicEncoder` and `IncrementalEncoder` (re-exported from the package
`__init__`), plus `SymbolEncoder` (SMT symbol management).

### Converter ([src/tempest/converter.py](src/tempest/converter.py))

`SMTConverter` is a `DagWalker` over UP expression trees that translates UP
`FNode` expressions into PySMT formulas (`walk_fluent_exp`, `walk_*_constant`,
`walk_param_exp`, ...).

### Configuration

Engines accept `params` via the UP planner factory. Common parameters:
`incremental`, `horizon`, `solver_name`. Optimal engines add
`ground_abstract_step`, `grounder_name`, `sat_before_opt`,
`secondary_objective` (`"weighted"` | `"lexicographic"` | `None`). See the
README's Parameters section.

## Versioning and release flow

Version lives in `pyproject.toml` → `[project].version`. Dev versions follow
PEP 440: `<base>.dev<N>+g<sha>` (e.g. `0.0.1.dev42+gabc1234`), where `N` =
`git rev-list --count HEAD`, stamped by
[ci/stamp_dev_version.py](ci/stamp_dev_version.py) in CI (never committed).

**Cut a release:**
```bash
just bump 0.1.0
git commit -am "release: v0.1.0"
git tag v0.1.0 && git push --follow-tags
```

The `v*` tag triggers [build-and-release.yml](.github/workflows/build-and-release.yml):
- `publish` → `pypa/gh-action-pypi-publish@release/v1` using **PyPI Trusted
  Publishing** (OIDC). The job declares a GitHub `environment` matching the
  pending publisher registered on PyPI for `up-tempest`; no API tokens in the repo.
- `github-release` → `softprops/action-gh-release@v3` with auto-generated notes
  and the wheel + sdist attached.

Both `github-release` and `dev-release` authenticate with an **installation
token from a release GitHub App** (`actions/create-github-app-token@v3`), not
`GITHUB_TOKEN`, because org policy locks workflow tokens to read-only.
Credentials live in repo secrets `RELEASER_APP_ID` and `RELEASER_APP_PRIVATE_KEY`.

On every push to `main`, `stamp-dev` runs, build produces a dev-versioned wheel,
and `dev-release` refreshes a rolling `dev` pre-release (`pip install --pre` to test).

## Tooling-related conventions

- All formatting via `ruff format` (config in `pyproject.toml` → `[tool.ruff.format]`).
- Mypy config in `pyproject.toml` → `[tool.mypy]`, scoped to `src/tempest`.
- **`tests/` is outside `src/`** (modern best practice).
- Ruff is scoped to `src tests ci`.
- No Rust: this is a pure-Python project (unlike the sibling `tamerlite` repo
  its tooling was modelled on).
