# -*- Mode: makefile -*- 
# Makefile.in for running the test cases for the CIL compiler
# Use from the test directory !!!
# author: George Necula
# hacks here and there by Wes and Scott

# this Makefile makes use of several GNU Make extensions; see
#   http://www.gnu.org/manual/make/html_chapter/make_toc.html

# pull in definitions from ./configure
include ../config.mk

TESTDIR := .

ifneq ($(ARCHOS), x86_WIN32)
ifneq ($(ARCHOS), x86_LINUX) 
ifneq ($(ARCHOS), x86_DARWIN) 
ifneq ($(ARCHOS), sparc_SOLARIS) 
   $(error You must set the ARCHOS variable to x86_WIN32, x86_LINUX, x86_DARWIN, or sparc_SOLARIS)
endif
endif
endif
endif

ifndef BIG_EXAMPLES
 BIG_EXAMPLES := ../../big-examples/
endif

defaulttarget:
	@echo "This Makefile is intended to be run with an explicit target."


# sm: find and remove all the intermediate files from translation
# sm: removed *box.c from those removed since $(TESTDIR)/PCC/src/pccbox.c should be kept
clean:
	-find . \( \
		-name '*~' -o \
		-name '*.cil.c' -o \
		-name '*.s' -o \
		-name '*.a' -o \
		-name '*.stackdump' -o \
		-name '*.exe' -o \
		-name '*.i' -o \
		-name '*_ppp.c' -o \
		-name '*.origi' -o \
		-name '*.o' -o \
		-name '*.obj' -o \
		-name '*.cabs.c' -o \
	        -name "*-tmp.c" -o \
		-name '*_comb*.c' -o \
		-name 'libmerge.a*' \
	\) -exec rm -f {} \;
	-find . -name '*.browser' -exec rm -rf {} \;


# sm: infer CILHOME when not set, to ease having multiple trees
ifndef CILHOME
  ifeq ($(ARCHOS), x86_WIN32)
    $(error You have not defined the CILHOME variable)
  else
    export CILHOME := $(shell pwd)/..
  endif
endif

CILLY := $(CILHOME)/bin/cilly
PATCHER := $(CILHOME)/bin/patcher

# Now do the user-specific customization
# It is Ok if this file does not exist
-include $(CILHOME)/.cilrc

# as a convenience, let RELEASE=1 on the command line imply
# all options designed to make things fast (at least when not in
# the middle of development)
ifdef RELEASE
  # use native code tools
  export NATIVECAML := 1
  export CILLY += -O2
endif

# By default we are on Linux
ifndef ARCHOS
  ARCHOS := x86_WIN32
endif

# By default use the old patcher
ifndef NEWPATCH
  OLDPATCH := 1
endif


# Now include the compiler specific stuff
ifdef _MSVC
  include ../Makefile.msvc
else
  ifdef _GNUCC
    include ../Makefile.gcc
  endif
endif


CILLY += --mode=$(COMPILERNAME) --decil

export EXTRAARGS


# CILLY contains arguments that are passed to cil
# Pass such arguments in the command line as EXTRAARGS="..."
# NOTE: you should *never* set EXTRAARGS within this Makefile,
# because *any* such settings will be overridden if someone
# specified EXTRAARGS on the command line
CILLY+= --save-temps $(EXTRAARGS)

ifndef NOCHECK
  CILLY += --strictcheck
endif

ifdef OCAMLDEBUG
  CILLY+= --ocamldebug
endif

ifdef NOLINES
  CILLY+= --noPrintLn
endif
ifdef COMMLINES
  CILLY+= --commPrintLn
endif

ifdef USECABS
  CILLY+= --usecabs
endif
ifndef NATIVECAML
  CILLY+= --bytecode
endif
ifdef VERBOSE
  CILLY+= --verbose --warnall
endif
ifdef KEEPMERGED
  CILLY+= --keepmerged
endif
ifdef MERGEONLY
  CILLY+= --keepmerged  --onlyMerge --mergeKeepAnnotations 
endif
ifdef CABSONLY
  CILLY+= --cabsonly
endif


# This is a way to enable the stats, allowing the command line to override it
# Do STATS= to disable the stats.
STATS := 1
ifdef STATS
  CILLY+= --stats
endif

# enable logging of all fn calls in the application
# (see LOGSTYLE, below)
ifdef LOGCALLS
  CILLY+= --logcalls
endif


# when SEPARATE is defined, merging is disabled
ifdef SEPARATE
  CILLY+= --nomerge
endif

# sm: this will make gcc warnings into errors; it's almost never
# what we want, but for a particular testcase (combine_copyptrs)
# I need it to show the difference between something which works
# and something which will cause inference problems later
ifdef WARNINGS_ARE_ERRORS
  CFLAGS += -Werror
endif


# Enable profiling
ifdef PROFILE
  CILLY+= -pg
endif

# sm: use this instead of "sh ./testit" for those self-tests which can't
# be made to work on windows; it does nothing, and has no output
UNIXTESTIT := sh ./testit


# ----------- below here are rules for building benchmarks --------

CC_OPTIMVARIANT:= $(CC) $(DEF)_$(COMPILERNAME) \
                 $(DEF)CIL \
                 $(INC)$(CILHOME)/include \
                 $(OPT_O2)

# use this dependency for those targets that must be built with GCC
mustbegcc :
ifndef _GNUCC
	@echo This test case works only with _GNUCC=1; exit 3
endif

mustbelinux:
ifneq ($(ARCHOS), x86_LINUX)
	@echo This test case works only on Linux; exit 3
endif


############ Small tests
SMALL1 := $(TESTDIR)/small1

test/% : $(SMALL1)/%.c 
	cd $(SMALL1); $(CILLY) --nomerge --commPrintLn \
	       $(CONLY) $(CFLAGS) $(ASMONLY)$*.s $*.c 
	echo SUCCESS

testobj/% : $(SMALL1)/%.c  
	cd $(SMALL1); $(CILLY) --nomerge  --commPrintLn  \
	       $(CONLY) $(CFLAGS) $(OBJOUT)$*.o $*.c 

testrun/% : $(SMALL1)/%.c  
	cd $(SMALL1); $(CILLY) --nomerge  --commPrintLn  \
	       $(CFLAGS) $(EXEOUT)$*.exe $*.c
	cd $(SMALL1); ./$*.exe
	echo SUCCESS

testrungcc/% : $(SMALL1)/%.c mustbegcc
	cd $(SMALL1); $(CILLY) --nomerge  --commPrintLn  \
	       $(CFLAGS) $(EXEOUT)$*.exe $*.c
	cd $(SMALL1); ./$*.exe
	echo SUCCESS

#preprocessed files:
test_i/% : $(SMALL1)/%.i 
	cd $(SMALL1); $(CILLY) --nomerge --commPrintLn \
	       $(CONLY) $(CFLAGS) $(ASMONLY)$*.s $*.i
	echo SUCCESS


# sm: some project members don't want the testing targets to depend
# on quickbuild (which rebuilds translator components whose dependencies
# have changed), and others do..
ifdef TARGETS_DEP_QUICKBUILD
  # with switch to test/Makefile, doesn't do what I want, so no-op
  #TARGET_DEP := quickbuild
  TARGET_DEP := 
endif

ifndef NOPRINTLN
 NOPRINTLN := --commPrintLn
endif

# sm: attempt at a single rule for my testing purposes
# gn: I added .exe so that I can delete the executables
scott/%: $(TESTDIR)/small2/%.c $(TARGET_DEP)
	rm -f $(TESTDIR)/small2/$*.exe
	cd $(TESTDIR)/small2; $(CC) $(CONLY) $(CFLAGS) $(WARNALL) $*.c
	cd $(TESTDIR)/small2; $(CILLY) --nomerge --save-temps=. \
                 $(CFLAGS) $(NOPRINTLN) \
                 $*.c \
                 $(EXEOUT)$*.exe
	bash -c "time $(TESTDIR)/small2/$*.exe"


# There are a few tests that CIL supports but recent versions of gcc don't.
# So don't try calling gcc on these.
scott-nogcc/%: $(TESTDIR)/small2/%.c $(TARGET_DEP)
	rm -f $(TESTDIR)/small2/$*.exe
	cd $(TESTDIR)/small2; $(CILLY) --nomerge --save-temps=. \
                 $(CFLAGS) $(NOPRINTLN) \
                 $*.c \
                 $(EXEOUT)$*.exe
	bash -c "time $(TESTDIR)/small2/$*.exe"

scott-nolink/%: $(TESTDIR)/small2/%.c $(TARGET_DEP)
	rm -f $(TESTDIR)/small2/$*.exe
	cd $(TESTDIR)/small2; $(CC) $(CONLY) $(WARNALL) $*.c
	cd $(TESTDIR)/small2; $(CILLY) --nomerge $(CONLY) --save-temps=. \
                 $(CFLAGS) $(WARNALL) $(NOPRINTLN) \
                 $*.c \
                 $(EXEOUT)$*.exe



ARCHOS := $(ARCHOS)
OBJDIR := $(CILHOME)/obj/$(ARCHOS)
ifdef NATIVECAML
 CMXA := cmxa
 CAMLC := ocamlopt
else
 CMXA := cma
 CAMLC := ocamlc -custom
endif

testrun/% : $(SMALL1)/%.ml
	$(CAMLC) -noautolink -I $(OBJDIR) unix.$(CMXA) str.$(CMXA) nums.$(CMXA) \
                 -cclib -lunix -cclib -lstr -cclib -lnums cil.$(CMXA) \
                 $(EXEOUT) $(basename $<).exe $<
	$(basename $<).exe
	echo SUCCESS


combine%: $(SMALL1)/combine%_1.c
	cd $(SMALL1); \
          $(CILLY) $(CFLAGS) \
                    $(notdir $(wildcard $(SMALL1)/combine$*_[1-9].c)) \
	            $(EXEOUT)combine$*.exe
	cd $(SMALL1); ./combine$*.exe

arcombine: mustbegcc
	cd $(SMALL1); $(CILLY) -c array1.c array2.c
	cd $(SMALL1); $(CILHOME)/bin/cilly \
                           --mode=AR --merge --verbose crv array.a array1.o array2.o
	cd $(SMALL1); $(CILLY) -o matrix.exe array.a matrix.c
	cd $(SMALL1); ./matrix.exe


# ww: Scott's structs-edg-stl.c example
structs : mustbemanju
	cd /usr/src/big-examples/; $(CILLY) --nomerge \
	       $(CONLY) $(CFLAGS) structs-edg-stl.c 
	echo SUCCESS



# sm: yet another failure-test target, this time utilizing a nomerge
# script capable of testing multiple failures per file
test-bad/%: $(TESTDIR)/small2/%.c $(TARGET_DEP)
ifdef _MSVC
ifndef RELEASE
	@echo ">>>>> Set RELEASE=1 when using MSVC to avoid those\
	pesky dialog boxes. <<<<<"
endif
endif
	cd $(TESTDIR)/small2; \
	  CILHOME="$(CILHOME)" \
	  CILLY="$(CILLY) --nomerge --commPrintLn" \
	  CFLAGS="$(CFLAGS) $(WARNALL)" \
          TESTBADONCE="$(TESTBADONCE)" \
	  _MSVC="$(_MSVC)" \
	  bash ../../bin/test-bad $*.c

test-bad1/%: $(TESTDIR)/small1/%.c $(TARGET_DEP)
	cd $(TESTDIR)/small1; \
	  CILHOME="$(CILHOME)" \
	  CILLY="$(CILLY) --nomerge --commPrintLn" \
	  CFLAGS=" $(CFLAGS) $(WARNALL)" \
          TESTBADONCE="$(TESTBADONCE)" \
	  _MSVC="$(_MSVC)" \
	  bash ../../bin/test-bad $*.c


#CCURED_NO_SIGABRT prevents cygwin from doing a memory dump on every failure
# case.
runall/%: $(TESTDIR)/small2/%.c $(TARGET_DEP)
	cd $(TESTDIR)/small2; \
	CCURED_NO_SIGABRT=1 \
	COMMAND="$(CILLY) \
	   $(CFLAGS) $(WARNALL) __FILE__  $(EXEOUT)__BASENAME__.exe \
	   && ./__BASENAME__.exe" \
	COMMENT="//" \
	 perl ../../ocamlutil/runall.pl $*.c


runall_syntax/%: $(TESTDIR)/small2/%.c $(TARGET_DEP)
	cd $(TESTDIR)/small2; \
	CCURED_NO_SIGABRT=1 \
	COMMAND="$(CILLY) \
	   $(CFLAGS) $(WARNALL) __FILE__  $(EXEOUT)__BASENAME__.exe \
	   && ./__BASENAME__.exe && cat __BASENAME__.cured.c" \
	COMMENT="//" \
	 perl ../../ocamlutil/runall.pl $*.c

# sm: trivial test of combiner
MYSAFECC := $(CILLY)
comb: $(TESTDIR)/small2/comb1.c $(TESTDIR)/small2/comb2.c 
	rm -f $(TESTDIR)/small2/comb.exe
	cd $(TESTDIR)/small2; \
	  $(MYSAFECC)  comb1.c $(CONLY) $(OBJOUT) comb1.o; \
	  $(MYSAFECC)  comb2.c $(CONLY) $(OBJOUT) comb2.o; \
	  $(MYSAFECC)  comb3.c $(CONLY) $(OBJOUT) comb3.o; \
	  $(MYSAFECC)  comb4.c $(CONLY) $(OBJOUT) comb4.o; \
          $(MYSAFECC)  comb1.o comb2.o comb3.o comb4.o $(EXEOUT)comb.exe
	$(TESTDIR)/small2/comb.exe

#call cilly on a .c file, a .i file, a .s file, and a .o file.
#Of course, only the first two are merged.
mixedcomb: $(TESTDIR)/small2/comb1.c $(TESTDIR)/small2/comb2.c 
	rm -f $(TESTDIR)/small2/comb.exe
	cd $(TESTDIR)/small2; \
	  gcc -E -o comb2.i comb2.c; \
	  gcc -S -o comb3.s comb3.c; \
	  gcc -c -o comb4.o comb4.c; \
	  $(MYSAFECC)  comb1.c comb2.i comb3.s comb4.o $(EXEOUT)comb.exe
	$(TESTDIR)/small2/comb.exe

# sm: another merger test
mergestruct: $(TESTDIR)/small2/mergestruct1.c $(TESTDIR)/small2/mergestruct2.c
	cd $(TESTDIR)/small2; \
	  $(CILLY) mergestruct1.c mergestruct2.c -o mergestruct.exe
	$(TESTDIR)/small2/mergestruct.exe

# sm: yet another merger test (I know there's a target somewhere)
mergeinline: $(TESTDIR)/small2/mergeinline1.c $(TESTDIR)/small2/mergeinline2.c
	cd $(TESTDIR)/small2; \
	  $(CILLY) mergeinline1.c mergeinline2.c -o mergeinline.exe
	$(TESTDIR)/small2/mergeinline.exe

# sm: test of combiner's ability to report inconsistencies
baddef: $(TESTDIR)/small2/baddef1.c $(TESTDIR)/small2/baddef2.c 
	cd $(TESTDIR)/small2; $(CC) baddef1.c baddef2.c -o baddef.exe \
           && ./baddef.exe
	rm -f $(TESTDIR)/small2/baddef.exe
	cd $(TESTDIR)/small2; \
	  $(MYSAFECC)  baddef1.c $(CONLY) $(OBJOUT) baddef1.o; \
	  $(MYSAFECC)  baddef2.c $(CONLY) $(OBJOUT) baddef2.o; \
          $(MYSAFECC)  baddef1.o baddef2.o $(EXEOUT)baddef.exe
	$(TESTDIR)/small2/baddef.exe




### Generic test
testfile/% : 
	$(CILLY) /TC $*

testdir/% : 
	make -C CC="ccured" $*


merge-ar:
	cd small2; $(CILHOME)/bin/cilly --merge -c merge-ar.c merge-twice-1.c
	cd small2; $(CILHOME)/bin/cilly --merge --mode=AR cr libmerge.a merge-ar.o merge-twice-1.o
	cd small2; $(CILHOME)/bin/cilly --merge libmerge.a -o merge-ar



