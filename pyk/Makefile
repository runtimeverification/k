K_ROOT := $(abspath ..)
K_BIN  := $(K_ROOT)/k-distribution/target/release/k/bin

export PATH := $(K_BIN):$(PATH)


.PHONY: default all clean build install                          \
        poetry-install                                           \
        test test-unit test-integration test-pyk                 \
        format isort autoflake black                             \
        check check-isort check-autoflake check-black check-mypy

default: check test-unit

all: check test

clean:
	rm -rf definitions dist src/pyk.egg-info .myp_cache
	find -type d -name __pycache__ -prune -exec rm -rf {} \;
	$(MAKE) -C pyk-tests clean

build:
	poetry build

install:
	pip3 install . --root=$(DESTDIR) --prefix=$(PREFIX)

poetry-install:
	poetry install

POETRY_RUN := poetry run

# Tests

PYK_TEST_ARGS :=

test: test-unit test-integration test-pyk test-kit

test-unit: poetry-install
	$(POETRY_RUN) python -m unittest discover tests --verbose $(PYK_TEST_ARGS)

test-integration: poetry-install
	$(POETRY_RUN) python -m unittest discover integration_tests --verbose $(PYK_TEST_ARGS)

test-pyk: poetry-install
	$(POETRY_RUN) $(MAKE) -C pyk-tests

test-kit: poetry-install
	$(POETRY_RUN) $(MAKE) -C kit-tests

# Checks and formatting

format: isort autoflake black
check: check-isort check-autoflake check-black check-mypy

isort: poetry-install
	$(POETRY_RUN) isort src

check-isort: poetry-install
	$(POETRY_RUN) isort --check src

autoflake: poetry-install
	$(POETRY_RUN) autoflake src    \
	  --in-place                   \
	  --recursive                  \
	  --expand-star-imports        \
	  --remove-all-unused-imports  \
	  --ignore-init-module-imports \
	  --remove-duplicate-keys      \
	  --remove-unused-variables

check-autoflake: poetry-install
	$(POETRY_RUN) autoflake src    \
	  --check                      \
	  --recursive                  \
	  --expand-star-imports        \
	  --remove-all-unused-imports  \
	  --ignore-init-module-imports \
	  --remove-duplicate-keys      \
	  --remove-unused-variables

black: poetry-install
	$(POETRY_RUN) black src

check-black: poetry-install
	$(POETRY_RUN) black --check src

check-mypy: poetry-install
	$(POETRY_RUN) mypy src
