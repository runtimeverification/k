MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
export KOMPILE_BACKEND?=java
include $(MAKEFILE_PATH)/../callCC/Makefile
export KOMPILE_FLAGS=--main-module CALLCC --syntax-module CALLCC-SYNTAX --transition strict
