K_ROOT := $(abspath ..)
K_BIN  := $(K_ROOT)/k-distribution/target/release/k/bin

export PATH := $(K_BIN):$(PATH)


.PHONY: default all clean build install          \
        poetry-install                           \
        test test-unit test-integration test-pyk \
        format isort autoflake black             \
        check check-isort check-autoflake check-black check-flake8 check-mypy

default: check test-unit

all: check test

clean:
	rm -rf dist .mypy_cache
	find -type d -name __pycache__ -prune -exec rm -rf {} \;
	$(MAKE) -C pyk-tests clean

build:
	poetry build

install: build
	pip3 install ./dist/*.whl --root=$(DESTDIR) --prefix=$(PREFIX)

poetry-install:
	poetry install

POETRY_RUN := poetry run


# Tests

TEST_ARGS :=
CHECK = git --no-pager diff --no-index -R

test: test-unit test-integration test-pyk test-kit

test-unit: poetry-install
	$(POETRY_RUN) pytest src/tests --maxfail=1 --verbose $(TEST_ARGS)

test-integration: poetry-install
	$(POETRY_RUN) pytest src/integration_tests --numprocesses=4 --durations=0 --maxfail=1 --verbose $(TEST_ARGS)

test-pyk: poetry-install
	$(POETRY_RUN) $(MAKE) -C pyk-tests

test-kit: poetry-install
	$(POETRY_RUN) $(MAKE) -C kit-tests CHECK="$(CHECK)"


# Checks and formatting

format: autoflake isort black
check: check-flake8 check-mypy check-autoflake check-isort check-black

check-flake8: poetry-install
	$(POETRY_RUN) flake8 src

check-mypy: poetry-install
	$(POETRY_RUN) mypy src

autoflake: poetry-install
	$(POETRY_RUN) autoflake --quiet --in-place src

check-autoflake: poetry-install
	$(POETRY_RUN) autoflake --quiet --check src

isort: poetry-install
	$(POETRY_RUN) isort src

check-isort: poetry-install
	$(POETRY_RUN) isort --check src

black: poetry-install
	$(POETRY_RUN) black src

check-black: poetry-install
	$(POETRY_RUN) black --check src


# GraphQL schema

SCHEMA_FILE := src/pyk/krepl_web/docs/schema.graphql
GEN_SCHEMA := $(POETRY_RUN) python3 -c 'from pyk.krepl_web.server.schema import SCHEMA ; print(SCHEMA)'

schema: poetry-install
	$(GEN_SCHEMA) > $(SCHEMA_FILE)
.PHONY: schema

check-schema: poetry-install
	echo "$$($(GEN_SCHEMA))" | diff $(SCHEMA_FILE) -
