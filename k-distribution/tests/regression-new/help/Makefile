DEF=test
EXT=test
TESTDIR=.
KRUN_FLAGS=--help
KOMPILE_FLAGS=--syntax-module TEST
PACKAGE_VERSION ?= $(shell cat ../../../../package/version)
GIT_REVISION=$(shell git describe --tags --long)
VERSION_REGEX="$(PACKAGE_VERSION)\|$(GIT_REVISION)"

1.test:
	${KAST}             --help    | grep -q -- "--version"
	${KDEP}             --help    | grep -q -- "--version"
	${KEQ}              --help    | grep -q -- "--version"
	${KOMPILE}          --help    | grep -q -- "--version"
	${KPROVE}           --help    | grep -q -- "--version"
	${KRUN}             --help    | grep -q -- "--version"
	${KSERVER}          --help    | grep -q -- "--version"
	${K_BIN}/kparse     --help    | grep -q -- "--version"
	${K_BIN}/kparse-gen --help    | grep -q -- "--version"
	${K_BIN}/kore-print --help    | grep -q -- "--version"
	${KAST}             --version | grep -q $(VERSION_REGEX)
	${KDEP}             --version | grep -q $(VERSION_REGEX)
	${KEQ}              --version | grep -q $(VERSION_REGEX)
	${KOMPILE}          --version | grep -q $(VERSION_REGEX)
	${KPROVE}           --version | grep -q $(VERSION_REGEX)
	${KRUN}             --version | grep -q $(VERSION_REGEX)
	${KSERVER}          --version | grep -q $(VERSION_REGEX)
	${K_BIN}/kparse     --version | grep -q $(VERSION_REGEX)
	${K_BIN}/kparse-gen --version | grep -q $(VERSION_REGEX)
	${K_BIN}/kore-print --version | grep -q $(VERSION_REGEX)


include ../../../include/kframework/ktest.mak

