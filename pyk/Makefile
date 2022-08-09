K_ROOT := $(abspath ..)
K_BIN  := $(K_ROOT)/k-distribution/target/release/k/bin

export PATH := $(K_BIN):$(PATH)


.PHONY: default all clean install                                  \
        $(VENV_DEV_DIR) $(VENV_PROD_DIR)                           \
        test test-unit test-integration test-pyk                   \
        check-code-style isort check-isort check-flake8 check-mypy

default: check-code-style test-unit

all: check-code-style test

clean:
	rm -rf $(VENV_DEV_DIR) $(VENV_PROD_DIR) definitions build src/pyk.egg-info .myp_cache
	find -type d -name __pycache__ -prune -exec rm -rf {} \;
	$(MAKE) -C pyk-tests clean


# Virtualenv

VENV_DEV_DIR := venv-dev
VENV_DEV     := $(VENV_DEV_DIR)/pyvenv.cfg
ACTIVATE_DEV := . $(VENV_DEV_DIR)/bin/activate

$(VENV_DEV):
	   virtualenv -p python3 $(VENV_DEV_DIR) \
	&& $(ACTIVATE_DEV)                       \
	&& pip install -r requirements/dev.txt

$(VENV_DEV_DIR): $(VENV_DEV)
	@echo $(ACTIVATE_DEV)


VENV_PROD_DIR := venv-prod
VENV_PROD     := $(VENV_PROD_DIR)/pyvenv.cfg
ACTIVATE_PROD := . $(VENV_PROD_DIR)/bin/activate

$(VENV_PROD):
	   virtualenv -p python3 $(VENV_PROD_DIR) \
	&& $(ACTIVATE_PROD)                       \
	&& pip install .

$(VENV_PROD_DIR): $(VENV_PROD)
	@echo $(ACTIVATE_PROD)

install:
	pip3 install . --root=$(DESTDIR) --prefix=$(PREFIX)


# Tests

PYK_TEST_ARGS :=

test: test-unit test-integration test-pyk

test-unit: $(VENV_DEV)
	$(ACTIVATE_DEV) && python3 -m unittest discover --verbose --top src pyk.tests $(PYK_TEST_ARGS)

test-integration: $(VENV_DEV)
	$(ACTIVATE_DEV) && python3 -m unittest discover --verbose --top src pyk.integration_tests $(PYK_TEST_ARGS)

test-pyk: $(VENV_PROD)
	$(ACTIVATE_PROD) && $(MAKE) -C pyk-tests
	rm -rf $(VENV_PROD_DIR) build src/pyk.egg-info


# Checks

check-code-style: check-isort check-flake8 check-mypy

isort: $(VENV_DEV)
	$(ACTIVATE_DEV) && isort src

check-isort: $(VENV_DEV)
	$(ACTIVATE_DEV) && isort --check src

check-flake8: $(VENV_DEV)
	$(ACTIVATE_DEV) && flake8 src

check-mypy: $(VENV_DEV)
	$(ACTIVATE_DEV) && mypy src

