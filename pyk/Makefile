.PHONY: all clean test integration-test                            \
        $(VENV_DEV_DIR) $(VENV_PROD_DIR)                           \
        check-code-style isort check-isort check-flake8 check-mypy


all: check-code-style test


# virtualenv

VENV_DEV_DIR := venv-dev
VENV_DEV     := $(VENV_DEV_DIR)/pyvenv.cfg
ACTIVATE_DEV := . $(VENV_DEV_DIR)/bin/activate

$(VENV_DEV):
	   virtualenv -p python3.8 $(VENV_DEV_DIR) \
	&& $(ACTIVATE_DEV)                         \
	&& pip install -r requirements/dev.txt

$(VENV_DEV_DIR): $(VENV_DEV)
	@echo $(ACTIVATE_DEV)


VENV_PROD_DIR := venv-prod
VENV_PROD     := $(VENV_PROD_DIR)/pyvenv.cfg
ACTIVATE_PROD := . $(VENV_PROD_DIR)/bin/activate

$(VENV_PROD):
	   virtualenv -p python3.8 $(VENV_PROD_DIR) \
	&& $(ACTIVATE_PROD)                         \
	&& pip install .

$(VENV_PROD_DIR): $(VENV_PROD)
	@echo $(ACTIVATE_PROD)


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
	rm -rf $(VENV_PROD_DIR) build src/pyk.egg-info

# Clean

clean:
	rm -rf $(VENV_DEV_DIR) $(VENV_PROD_DIR) build src/pyk.egg-info .myp_cache
	find -type d -name __pycache__ -prune -exec rm -rf {} \;
	$(MAKE) -C integration_tests clean
