MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
include $(MAKEFILE_PATH)/../../Makefile
KOMPILE_FLAGS=--transition "division lookup increment assignment read print strict"
KOMPILE_BACKEND?=java
KRUN_FLAGS=--search --pattern '<k> .K </k> <output> _:List ListItem(\#buffer(S:String)) </output>'
