# CIL_BASE = ../cil
# CIL_PLATFORM ?= $(firstword $(shell ls $(CIL_BASE)/obj))
# no warnings
OCAMLOPT_FLAGS = -w a -warn-error a 
# all warnings
#OCAMLOPT_FLAGS = -w A -warn-error A

# CIL = $(CIL_BASE)/obj/$(CIL_PLATFORM)

OCAML_COMPILE = ocamlopt $(OCAMLOPT_FLAGS) -c -I ioxml

OCAML_LEX = ocamllex
OCAML_YACC = ocamlyacc
OCAML_LINK = ocamlopt $(OCAMLOPT_FLAGS) -I ioxml -ccopt -L./ioxml

# these are partially ordered by inclusion.  don't know how to avoid manually ordering these
MODULES = errormsg.cmx longarray.cmx growArray.cmx escape.cmx cabshelper.cmx whitetrack.cmx cprint.cmx lexerhack.cmx cabs.cmx clexer.cmx cparser.cmx frontc.cmx cabsPrinter.cmx cabsDriver.cmx
# xmlPrinter.cmx 

#IOXML = ioxml/ioXML.cmx ioxml/pa_ioXML.cmo
IOXML = 
.PHONY: all cleanOnMakefileChange clean ioxml
all: cparser 

# $(IOXML): ioxml/ioXML.ml ioxml/ioXML.mli ioxml/pa_ioXML.ml
# make -C ioxml all
		
# xmlPrinter.ml: cabs.ml $(IOXML)
# camlp5o ioxml/pa_ioXML.cmo pr_o.cmo -sep "\n\n" cabs.ml > xmlPrinter.tmp
# sed -i '2 i open Cabs' xmlPrinter.tmp
# mv xmlPrinter.tmp xmlPrinter.ml
	
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
# cabsPrinter.cmx cabsPrinter.cmi: cabs.cmi escape.cmi xmlPrinter.cmi
# xmlPrinter.cmx xmlPrinter.cmi: $(IOXML)
%.cmx %.cmi: %.ml 
#Makefile
	$(OCAML_COMPILE) $*.ml
	
cparser.cmi: cparser.mli cabs.cmi clexer.ml
	$(OCAML_COMPILE) cparser.mli
	
cabsDriver.cmx cabsDriver.cmi: cabsPrinter.cmi

cparser: $(MODULES)
	$(OCAML_LINK) -o $@ unix.cmxa str.cmxa nums.cmxa $^
# $(OCAML_LINK) -o $@ unix.cmxa str.cmxa nums.cmxa ioXML.cmx $^

clean:
	rm -f *.cmi *.cmx *.o *.mli *.cil xmlPrinter.ml cparser.ml clexer.ml *.preprocessed cparser.exe cparser *.stackdump
	make -C ioxml clean
