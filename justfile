set shell := ["bash", "-cu"]

default:
    @just --list

# Sync the environment from uv.lock (project + dev group)
install:
    uv sync

# Run pytest. Set PYTHONPATH externally for the UP fixtures (up_test_cases).
# The z3 tests work out of the box; for the OptiMathSAT cases, first run:
#   uv run --with setuptools pysmt-install --optimsat --confirm-agreement
test:
    uv run pytest tests/ -v

# Run all lint and formatting checks. Fails if any issues are found.
lint:
    uv run ruff check src tests ci
    uv run ruff format --check src tests ci

# Apply the formatter and auto-fix lint issues where possible
format:
    uv run ruff format src tests ci
    uv run ruff check --fix src tests ci

# Static type checking
typecheck:
    uv run mypy

# Run all pre-commit hooks against the whole repo
precommit:
    uv run pre-commit run --all-files --show-diff-on-failure

# Build sdist + wheel for the up-tempest package (hatchling).
build:
    uv build

# Bump the version in pyproject.toml and refresh uv.lock
bump version:
    sed -i 's/^version = ".*"/version = "{{version}}"/' pyproject.toml
    uv lock
    @echo "Now: git commit -am 'release: v{{version}}' && git tag v{{version}} && git push --follow-tags"

# Remove build, cache, and tooling artifacts
clean:
    rm -rf build/ dist/ .mypy_cache/ .pytest_cache/ .ruff_cache/
