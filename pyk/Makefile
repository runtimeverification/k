.PHONY: all test check-code-style isort check-isort check-flake8 test-mypy

all: check-code-style test


# virtualenv

VENV     := venv/pyvenv.cfg
ACTIVATE := . venv/bin/activate

$(VENV):
	   virtualenv -p python3.8 venv        \
	&& $(ACTIVATE)                         \
	&& pip install -r requirements/dev.txt



# Checks

check-code-style: check-isort check-flake8 check-mypy

isort: $(VENV)
	$(ACTIVATE) && isort src integration_tests

check-isort: $(VENV)
	$(ACTIVATE) && isort --check src integration_tests

check-flake8: $(VENV)
	$(ACTIVATE) && flake8 src integration_tests

check-mypy: $(VENV)
	$(ACTIVATE) && mypy src integration_tests


# Tests

test: $(VENV)
	$(ACTIVATE) && python3 -m unittest discover --start-directory src


# Clean

clean:
	rm -rf venv
	rm -rf .mypy_cache
	find -type d -name __pycache__ -prune -exec rm -rf {} \;
