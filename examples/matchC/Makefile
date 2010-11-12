K_ROOT_DIR = $(HOME)/k-framework
ML_ROOT_DIR = $(K_ROOT_DIR)/examples/matchC

ANTLR_ROOT_DIR = $(K_ROOT_DIR)/tools/antlr
ANTLR_MAKEFILE = Makefile.antlr
PARSER_DIR = $(ML_ROOT_DIR)/parser
PARSER_MAKEFILE = Makefile
SEMANTICS_DIR = $(ML_ROOT_DIR)/semantics
SEMANTICS_MAKEFILE = Makefile


all:  build

build:
	$(MAKE) -C $(ANTLR_ROOT_DIR) -f $(ANTLR_MAKEFILE)
	$(MAKE) -C $(PARSER_DIR) -f $(PARSER_MAKEFILE)
	$(MAKE) -C $(SEMANTICS_DIR) -f $(SEMANTICS_MAKEFILE)

clean:
	$(MAKE) -C $(ANTLR_ROOT_DIR) -f $(ANTLR_MAKEFILE) clean
	$(MAKE) -C $(PARSER_DIR) -f $(PARSER_MAKEFILE) clean
	$(MAKE) -C $(SEMANTICS_DIR) -f $(SEMANTICS_MAKEFILE) clean

