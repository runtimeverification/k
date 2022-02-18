.PHONY: all test test-code-style test-flake8 test-isort isort

all: test

test: test-code-style

test-code-style: test-flake8 test-isort

test-flake8:
	flake8 . --ignore=E501

test-isort:
	isort . --check

isort:
	isort .
