MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
ifeq (,$(wildcard ${MAKEFILE_PATH}/../include/ktest.mak))
export K_HOME=/usr/lib/kframework
else
export K_HOME=${MAKEFILE_PATH}/..
endif
