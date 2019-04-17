DEF=test
EXT=test
TESTDIR=.
KRUN_FLAGS=--help

1.test:
	${KAST} --help | grep -q -- "--version"
	${KDEP} --help | grep -q -- "--version"
	${KEQ} --help | grep -q -- "--version"
	${KOMPILE} --help | grep -q -- "--version"
	${KPROVE} --help | grep -q -- "--version"
	${KRUN} --help | grep -q -- "--version"
	${KSERVER} --help | grep -q -- "--version"
	${KAST} --version | grep -q RV-K
	${KDEP} --version | grep -q RV-K
	${KEQ} --version | grep -q RV-K
	${KOMPILE} --version | grep -q RV-K
	${KPROVE} --version | grep -q RV-K
	${KRUN} --version | grep -q RV-K
	${KSERVER} --version | grep -q RV-K


include ../../../include/ktest.mak

