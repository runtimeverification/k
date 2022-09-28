.PHONY: default all clean build install          \
        poetry-install                           \
        format isort autoflake black             \
        check check-isort check-autoflake check-black check-flake8 check-mypy

default: check

clean:
	rm -rf dist .mypy_cache
	find -type d -name __pycache__ -prune -exec rm -rf {} \;

build:
	poetry build

poetry-install:
	poetry install

POETRY_RUN := poetry run


# Checks and formatting

format: isort autoflake black
check: check-isort check-autoflake check-black check-flake8 check-mypy

isort: poetry-install
	$(POETRY_RUN) isort src

check-isort: poetry-install
	$(POETRY_RUN) isort --check src

autoflake: poetry-install
	$(POETRY_RUN) autoflake --quiet --in-place src

check-autoflake: poetry-install
	$(POETRY_RUN) autoflake --quiet --check src

check-flake8: poetry-install
	$(POETRY_RUN) flake8 src

black: poetry-install
	$(POETRY_RUN) black src

check-black: poetry-install
	$(POETRY_RUN) black --check src

check-mypy: poetry-install
	$(POETRY_RUN) mypy src
