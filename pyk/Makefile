.PHONY: all test integration-test check-code-style isort check-isort check-flake8 test-mypy

all: check-code-style test


# virtualenv

VENV_DEV     := venv-dev/pyvenv.cfg
ACTIVATE_DEV := . venv-dev/bin/activate

$(VENV_DEV):
	   virtualenv -p python3.8 venv-dev    \
	&& $(ACTIVATE_DEV)                     \
	&& pip install -r requirements/dev.txt


VENV_PROD     := venv-prod/pyvenv.cfg
ACTIVATE_PROD := . venv-prod/bin/activate

$(VENV_PROD):
	   virtualenv -p python3.8 venv-prod \
	&& $(ACTIVATE_PROD)                  \
	&& pip install .


# Checks

check-code-style: check-isort check-flake8 check-mypy

isort: $(VENV_DEV)
	$(ACTIVATE_DEV) && isort src integration_tests

check-isort: $(VENV_DEV)
	$(ACTIVATE_DEV) && isort --check src integration_tests

check-flake8: $(VENV_DEV)
	$(ACTIVATE_DEV) && flake8 src integration_tests

check-mypy: $(VENV_DEV)
	$(ACTIVATE_DEV) && mypy src integration_tests


# Tests

test: $(VENV_DEV)
	$(ACTIVATE_DEV) && python3 -m unittest discover --start-directory src

integration-test: $(VENV_PROD)
	$(ACTIVATE_PROD) && $(MAKE) -C integration_tests
	rm -rf venv-prod build src/pyk.egg-info

# Clean

clean:
	rm -rf venv-dev venv-prod build src/pyk.egg-info .myp_cache
	find -type d -name __pycache__ -prune -exec rm -rf {} \;
	$(MAKE) -C integration_tests clean
