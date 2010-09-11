CIL_BASE = ../cil
CIL_PLATFORM ?= $(firstword $(shell ls $(CIL_BASE)/obj))
OCAMLOPT_FLAGS = -w a -warn-error a

CIL = $(CIL_BASE)/obj/$(CIL_PLATFORM)

OCAML_COMPILE = ocamlopt $(OCAMLOPT_FLAGS) -c -I $(CIL)
OCAML_LINK = ocamlopt $(OCAMLOPT_FLAGS) -I $(CIL) -ccopt -L$(CIL)
 
.PHONY: all cleanOnMakefileChange clean
all: cparser 

$(CIL)/cil.cmxa:
	cd $(CIL_BASE) && autoconf && ./configure
	make -C $(CIL_BASE)
	
cabsDriver.cmx cabsDriver.cmi: $(CIL)/cil.cmxa cabsDriver.ml cabsPrinter.cmi
	$(OCAML_COMPILE) cabsDriver.ml	
		
cabsPrinter.cmx cabsPrinter.cmi: $(CIL)/cil.cmxa cabsPrinter.ml
	$(OCAML_COMPILE) cabsPrinter.ml
	
cparser: cabsPrinter.cmx cabsDriver.cmx
	$(OCAML_LINK) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa $^


clean:
	rm -f *.cmi *.cmx *.o *.cil *.preprocessed cparser.exe cparser *.stackdump
