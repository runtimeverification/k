CIL_BASE = ../cil
CIL_PLATFORM ?= $(firstword $(shell ls $(CIL_BASE)/obj))
OCAMLOPT_FLAGS = -w a -warn-error a

CIL = $(CIL_BASE)/obj/$(CIL_PLATFORM)

OCAML_COMPILE = ocamlopt $(OCAMLOPT_FLAGS) -c -I $(CIL)
OCAML_LINK = ocamlopt $(OCAMLOPT_FLAGS) -I $(CIL) -ccopt -L$(CIL)
 
.PHONY: all cleanOnMakefileChange clean 
all: cparser 

$(CIL)/cil.cmxa:
	cd $(CIL_BASE); ./configure
	make -C $(CIL_BASE)

maudeVisitor.cmx maudeVisitor.cmi: $(CIL)/cil.cmxa maudeVisitor.ml
	echo $(CIL)
	$(OCAML_COMPILE) maudeVisitor.ml
	
maudePrinter.cmx maudePrinter.cmi: $(CIL)/cil.cmxa maudePrinter.ml defaultMaudePrinter.cmi
	$(OCAML_COMPILE) maudePrinter.ml
	
defaultMaudePrinter.cmx defaultMaudePrinter.cmi: $(CIL)/cil.cmxa defaultMaudePrinter.ml
	$(OCAML_COMPILE) defaultMaudePrinter.ml
	
cildriver.cmx cildriver.cmi: $(CIL)/cil.cmxa cildriver.ml maudeVisitor.cmi maudePrinter.cmi
	$(OCAML_COMPILE) cildriver.ml 

cparser: $(CIL)/cil.cmxa maudeVisitor.cmx defaultMaudePrinter.cmx maudePrinter.cmx cildriver.cmx 
	$(OCAML_LINK) -o cparser unix.cmxa str.cmxa nums.cmxa cil.cmxa maudeVisitor.cmx defaultMaudePrinter.cmx maudePrinter.cmx cildriver.cmx
	
	
cabsDriver.cmx cabsDriver.cmi: $(CIL)/cil.cmxa cabsDriver.ml cabsPrinter.cmi
	$(OCAML_COMPILE) cabsDriver.ml	
		
cabsPrinter.cmx cabsPrinter.cmi: $(CIL)/cil.cmxa cabsPrinter.ml
	$(OCAML_COMPILE) cabsPrinter.ml
	
cabsParser: $(CIL)/cil.cmxa cabsPrinter.cmx cabsDriver.cmx
	$(OCAML_LINK) -o $@ unix.cmxa str.cmxa nums.cmxa cil.cmxa $^


clean:
	rm -f *.cmi *.cmx *.o *.cil *.preprocessed cparser.exe cparser *.stackdump
