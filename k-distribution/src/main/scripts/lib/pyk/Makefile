.PHONY: all test check-code-style isort check-isort check-flake8 test-mypy

all: check-code-style test


# virtualenv

VENV     := venv/pyvenv.cfg
ACTIVATE := . venv/bin/activate

$(VENV):
	   virtualenv -p python3.8 venv    \
	&& $(ACTIVATE)                     \
	&& pip install -r requirements.txt



# Checks

check-code-style: check-isort check-flake8 check-mypy

isort: $(VENV)
	$(ACTIVATE) && isort ./pyk

check-isort: $(VENV)
	$(ACTIVATE) && isort ./pyk --check

check-flake8: $(VENV)
	$(ACTIVATE) && flake8 ./pyk --ignore=E501

check-mypy: $(VENV)
	$(ACTIVATE) && mypy ./pyk


# Tests

test: $(VENV)
	$(ACTIVATE) && python3 -m unittest


# Clean

clean:
	rm -rf venv
	rm -rf .mypy_cache
	find -type d -name __pycache__ -prune -exec rm -rf {} \;
