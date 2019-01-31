MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
include $(MAKEFILE_PATH)/../callCC/Makefile
KOMPILE_FLAGS=--main-module CALLCC --syntax-module CALLCC-SYNTAX
KOMPILE_BACKEND?=java
