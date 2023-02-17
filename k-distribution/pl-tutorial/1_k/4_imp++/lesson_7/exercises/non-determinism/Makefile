MAKEFILE_PATH := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
include $(MAKEFILE_PATH)/../../Makefile.concrete
KRUN_FLAGS=--search --pattern '<output> _:List ListItem(\#buffer(S:String)) </output>'
