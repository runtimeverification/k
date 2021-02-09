MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
ifneq (,$(wildcard ${MAKEFILE_PATH}/../../../include/kframework/ktest.mak))
export K_HOME?=${MAKEFILE_PATH}/../../../
else ifneq (,$(wildcard ${MAKEFILE_PATH}/../include/kframework/ktest.mak))
export K_HOME?=${MAKEFILE_PATH}/..
else ifneq (,$(wildcard /usr/include/kframework/ktest.mak))
export K_HOME?=/usr
else ifneq (,$(wildcard /usr/local/include/kframework/ktest.mak))
export K_HOME?=/usr/local
else
$(error "Could not find installation of K. Please set K_HOME environment variable to your K installation.")
endif
