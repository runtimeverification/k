.PHONY: all check-code-style isort check-isort check-flake8 test-mypy 

all: check-code-style

check-code-style: check-isort check-flake8 check-mypy

isort:
	isort ./pyk

check-isort:
	isort ./pyk --check

check-flake8:
	flake8 ./pyk --ignore=E501

check-mypy:
	mypy ./pyk
