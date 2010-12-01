# CIL_BASE = ../cil
# CIL_PLATFORM ?= $(firstword $(shell ls $(CIL_BASE)/obj))
# no warnings
OCAMLOPT_FLAGS = -w a -warn-error a 
# all warnings
#OCAMLOPT_FLAGS = -w A -warn-error A 

# CIL = $(CIL_BASE)/obj/$(CIL_PLATFORM)

OCAML_COMPILE = ocamlopt $(OCAMLOPT_FLAGS) -c -I .

OCAML_LEX = ocamllex
OCAML_YACC = ocamlyacc
OCAML_LINK = ocamlopt $(OCAMLOPT_FLAGS) -I . -ccopt -L.

# these are partially ordered by inclusion.  don't know how to avoid manually ordering these
MODULES = errormsg.cmx longarray.cmx growArray.cmx escape.cmx cabshelper.cmx whitetrack.cmx cprint.cmx lexerhack.cmx cabs.cmx clexer.cmx cparser.cmx frontc.cmx cabsPrinter.cmx cabsDriver.cmx

 
.PHONY: all cleanOnMakefileChange clean
all: cparser 

clexer.ml: clexer.mll
	$(OCAML_LEX) clexer.mll

cparser.ml cparser.mli: cparser.mly
	$(OCAML_YACC) cparser.mly

lexerhack.cmx lexerhack.cmi: errormsg.cmi
whitetrack.cmx whitetrack.cmi: cabs.cmi cabshelper.cmi
escape.cmx escape.cmi: whitetrack.cmi
cprint.cmx cprint.cmi: escape.cmi cabs.cmi
longarray.cmx longarray.cmi: errormsg.cmi
growArray.cmx growArray.cmi: errormsg.cmi longarray.cmi 	
cabshelper.cmx cabshelper.cmi: errormsg.cmi growArray.cmi cabs.cmi
cparser.cmx: cabs.cmi cabshelper.cmi lexerhack.cmi cprint.cmi
cabsDriver.cmx cabsDriver.cmi: cparser.cmi frontc.cmi clexer.cmi
frontc.cmx frontc.cmi: errormsg.cmi whitetrack.cmi cprint.cmi clexer.cmi
clexer.cmx clexer.cmi: lexerhack.cmi cparser.cmi cabshelper.cmi
cabsPrinter.cmx cabsPrinter.cmi: cabs.cmi escape.cmi
%.cmx %.cmi: %.ml Makefile
	$(OCAML_COMPILE) $*.ml
	
cparser.cmi: cparser.mli cabs.cmi clexer.ml
	$(OCAML_COMPILE) cparser.mli
	
cabsDriver.cmx cabsDriver.cmi: cabsPrinter.cmi

cparser: $(MODULES)
	$(OCAML_LINK) -o $@ unix.cmxa str.cmxa nums.cmxa $^

clean:
	rm -f *.cmi *.cmx *.o *.mli *.cil cparser.ml clexer.ml *.preprocessed cparser.exe cparser *.stackdump
