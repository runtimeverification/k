MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
export KOMPILE_BACKEND?=java
include $(MAKEFILE_PATH)/../../Makefile
export KOMPILE_FLAGS=--main-module CALLCC --transition strict
