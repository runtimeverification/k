K_VERSION := $(shell ./KVERSION)

MAKEFILE_PATH := $(abspath $(lastword $(MAKEFILE_LIST)))
MAKEFILE_DIR  := $(dir $(MAKEFILE_PATH))

VENV_DIR := venv
ACTIVATE := . $(VENV_DIR)/bin/activate
VENV     := $(VENV_DIR)/pyvenv.cfg

KOMPILED_DIR := kompiled


.PHONY: $(VENV_DIR)


# kompile

$(KOMPILED_DIR)/timestamp: assign.k transform.py $(VENV)
	   $(ACTIVATE) \
	&& kompile assign.k --backend haskell --output-definition kompiled --post-process 'python3 $(MAKEFILE_DIR)transform.py'


# virtualenv

$(VENV):
	   virtualenv -p python3.8 $(VENV_DIR) \
	&& $(ACTIVATE)                         \
	m
	&& pip install git+https://github.com/runtimeverification/k.git@${K_VERSION}#subdirectory=pyk

$(VENV_DIR): $(VENV)
	@echo $(ACTIVATE)
