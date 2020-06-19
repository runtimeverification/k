MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
KOMPILE_BACKEND?=java
include $(MAKEFILE_PATH)/../../Makefile
KOMPILE_FLAGS=--transition "division lookup increment assignment read print strict"
KRUN_FLAGS=--search --pattern '<k> .K </k> <output> _:List ListItem(\#buffer(S:String)) </output>'
