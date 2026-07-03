# Contributing to TemPEST

Thanks for wanting to contribute to TemPEST. This file covers both the
practical "how do I run X" side of the repo and the community process
(asking questions, reporting bugs, proposing changes, signing the CLA).

**Community process:** [Code of Conduct](#code-of-conduct) ·
[Asking questions](#asking-questions) ·
[Reporting bugs](#reporting-bugs) ·
[Suggesting enhancements](#suggesting-enhancements) ·
[Contribution workflow](#contribution-workflow) ·
[CLA](#contributor-license-agreement-cla)

**[Developer guide](#developer-guide):**
[Setup](#setup) ·
[Common tasks](#common-tasks-via-just) ·
[Test suite](#running-the-test-suite)

**[For maintainers](#for-maintainers):**
[Cutting a release](#cutting-a-release) ·
[Dependencies](#keeping-dependencies-fresh)

## Code of Conduct

This project follows the [Contributor Covenant Code of Conduct](CODE_OF_CONDUCT.md).
By participating, you agree to uphold it. Report unacceptable behaviour
to <pso-tools@fbk.eu>; reports are handled confidentially.

## Asking questions

For usage questions, in order:

1. Check the [README](README.md) and the runnable
   [demo notebook](doc/tempest_demo.ipynb).
2. Search [open and closed issues](https://github.com/fbk-pso/tempest/issues?q=is%3Aissue).
3. If still unanswered, open a [new issue](https://github.com/fbk-pso/tempest/issues/new)
   with the `question` label. Include your TemPEST version
   (`pip show up-tempest`), Python version, and OS.

## Reporting bugs

Before filing a bug:

- Confirm you're on the latest TemPEST version.
- Search [existing issues](https://github.com/fbk-pso/tempest/issues?q=is%3Aissue+label%3Abug)
  to avoid duplicates.

A useful bug report includes:

- A **minimal reproducible example**: the planning problem (PDDL or UP
  Python snippet), the engine and solver parameters, expected vs. actual
  output.
- The full stack trace, if any.
- Versions: `pip show up-tempest pysmt unified-planning`,
  `python --version`, OS.
- Which SMT/OMT solver you used (e.g. `z3`, `optimsat`) and how it was
  installed (`pysmt-install`).

Reports without a reproduction get labelled `needs-repro` and won't be
actively worked on until reproducible.

## Suggesting enhancements

For new features, search the issues for prior discussion and then open
one yourself, **before writing code**. Describe:

- The use case and *why it benefits the broader project*, not only your
  immediate need.
- A sketch of the proposed API or behaviour.
- Any alternatives you considered.

This lets us catch scope / design issues early and saves you from
writing a PR that needs to be redone.

## Contribution workflow

For non-trivial changes:

1. Open an issue first (or comment on an existing one) to align on
   scope and approach.
2. Fork the repo and create a feature branch off `main`:
   `git checkout -b feat/short-description`.
3. Make focused, well-described commits. Behaviour changes should come
   with new or updated tests.
4. Run `just precommit` locally — it must be green (this is the same
   command CI's lint job runs).
5. Run `just test` (see [Running the test suite](#running-the-test-suite)) —
   CI runs the full test matrix, so catch failures locally first.
6. Push to your fork and open a pull request against `main`. Give the PR
   a clear, user-facing title: release notes are auto-generated from PR
   titles, so your title becomes a release-note line verbatim.
7. On your first PR the [CLA assistant](https://cla-assistant.io/) bot
   will ask you to sign the CLA — see the next section.
8. Address review comments.

Typo fixes and tiny doc tweaks can skip the issue step and go straight
to a PR.

## Contributor License Agreement (CLA)

Before your first contribution can be merged, you must sign the
**FBK PSO Unit Individual Contributor License Agreement**:

- [CLA text](https://gist.github.com/alvalentini/a8c5e371be4e7e43b79035c67dc2a1ac)

TemPEST itself is released under the [GPL-3.0](LICENSE); the CLA
defines the licence terms under which you grant FBK the right to use
your contributions across all `fbk-pso` open-source projects.
On your first PR, the [cla-assistant](https://cla-assistant.io/) bot
posts a comment with a sign-in link; you authenticate with GitHub
OAuth and click "I agree". The signature applies to every subsequent
contribution you make to any project under the
[fbk-pso](https://github.com/fbk-pso) organisation.

**Exemptions:** FBK PSO Unit staff (whose contributions are governed
by their employment contracts) and automated accounts (bots) are
whitelisted in the cla-assistant configuration and skip the prompt.

## Developer guide

### Setup

Prerequisites:

- Python 3.10+
- [uv](https://github.com/astral-sh/uv) — Python project / environment manager
- [just](https://github.com/casey/just) — command runner (install with
  `uv tool install rust-just` or your package manager)

Clone and bootstrap:

```bash
git clone https://github.com/fbk-pso/tempest.git
cd tempest
uv sync                      # .venv + dev deps (z3 is a mandatory dependency)
uv run pre-commit install    # one-time
# Optional: OptiMathSAT, needed for the full test suite (z3 already installed):
uv run --with setuptools pysmt-install --optimsat --confirm-agreement
```

This repo uses **uv** for environment/dependency management (single
`uv.lock`), **ruff** for lint+format, **mypy** for type-checking,
**pre-commit** for hooks (enforced in CI), and **just** as the unified
task runner.

### Common tasks (via `just`)

| Recipe            | What it does                                                                           |
|-------------------|----------------------------------------------------------------------------------------|
| `just install`    | `uv sync`                                                                               |
| `just test`       | `uv run pytest tests/ -v`                                                               |
| `just lint`       | `ruff check` + `ruff format --check` over `src tests ci`                               |
| `just format`     | `ruff format` + `ruff check --fix` over `src tests ci`                                  |
| `just typecheck`  | `uv run mypy` (config in `pyproject.toml`, scope `src/tempest`)                         |
| `just precommit`  | `pre-commit run --all-files --show-diff-on-failure` (same command CI's lint job runs)  |
| `just build`      | `uv build` — produce the `up-tempest` sdist + wheel into `./dist/`                     |
| `just bump VERSION` | Update the version in `pyproject.toml` and refresh `uv.lock`                          |
| `just clean`      | Remove build / dist / cache directories                                                |

### Running the test suite

The test suite needs `unified-planning` (installed by `uv sync` from a
pinned git commit) and SMT/OMT solvers. The engine tests in
[tests/test_horizon.py](tests/test_horizon.py) exercise both `z3` (a mandatory
dependency, always present) and `optimsat` (installed via `pysmt-install`):

```bash
uv sync
uv run --with setuptools pysmt-install --optimsat --confirm-agreement
just test
```

The benchmark problems used by the tests live in [benchmarks/](benchmarks/)
and are discovered automatically. CI additionally runs the Unified
Planning report over several engine configurations
([test_specific_engine.yml](.github/workflows/test_specific_engine.yml)).

## For maintainers

The rest of this file covers operations that need push or merge rights
on the repo.

### Cutting a release

```bash
just bump 0.1.0
git commit -am "release: v0.1.0"
git tag v0.1.0 && git push --follow-tags
```

The push of a `v*` tag triggers
[build-and-release.yml](.github/workflows/build-and-release.yml), which:

- Publishes `up-tempest` to PyPI via **Trusted Publishing** (OIDC; no API
  tokens in the repo). The publish job is gated by a GitHub environment
  matching the pending publisher registered on PyPI for `up-tempest`.
- Creates an immutable GitHub Release `vX.Y.Z` with auto-generated notes
  (from PR titles since the previous tag) and the built wheel + sdist
  attached.

The `dev-release` and `github-release` jobs authenticate with an
installation token from a release GitHub App (because the org policy
locks `GITHUB_TOKEN` to read-only). Credentials live in two repo
secrets: `RELEASER_APP_ID` and `RELEASER_APP_PRIVATE_KEY`.

On every push to `main`, `stamp-dev` derives a PEP 440 dev version
(`0.0.1.devN+g<sha>`), the build job produces a dev-versioned wheel, and
`dev-release` refreshes a rolling `dev` pre-release under
[Releases](https://github.com/fbk-pso/tempest/releases/tag/dev) so you can
`pip install --pre` the latest `main` without building locally.

### Keeping dependencies fresh

Dependabot is configured ([.github/dependabot.yml](.github/dependabot.yml))
to open weekly PRs against two ecosystems:

- **uv** (Python deps) — including the git-tracked `unified-planning`
  dependency: a PR lands whenever the upstream `main` moves.
- **github-actions** — pinned action versions in workflows, grouped into a
  single PR per week to cut noise.

Just review the PR's diff, let CI run, and merge if green.

**`z3-solver` is exempt from Dependabot** ([.github/dependabot.yml](.github/dependabot.yml)):
its version is dictated by PySMT (see `pysmt/cmd/install.py`), not z3's own
release cadence. When you bump `pysmt`, check the `z3` version PySMT installs
there and update the `z3-solver` pin in [pyproject.toml](pyproject.toml) to
match.
