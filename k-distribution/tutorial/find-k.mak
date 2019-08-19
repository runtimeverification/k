MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
ifneq (,$(wildcard ${MAKEFILE_PATH}/../include/ktest.mak))
export K_HOME?=${MAKEFILE_PATH}/..
else ifneq (,$(wildcard /usr/lib/kframework/include/ktest.mak))
export K_HOME?=/usr/lib/kframework
else ifneq (,$(wildcard /usr/local/lib/kframework/include/ktest.mak))
export K_HOME?=/usr/local/lib/kframework
else
$(error "Could not find installation of K. Please set K_HOME environment variable to your K installation.")
endif
