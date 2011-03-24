K_ROOT_DIR = $(HOME)/k-framework
ML_ROOT_DIR = $(K_ROOT_DIR)/examples/matchC

PARSER_DIR = $(ML_ROOT_DIR)/parser
SEMANTICS_DIR = $(ML_ROOT_DIR)/semantics
VIEWER_DIR = $(ML_ROOT_DIR)/bin


all:  build

build:
	$(MAKE) -C $(PARSER_DIR)
	$(MAKE) -C $(SEMANTICS_DIR)
	$(MAKE) -C $(VIEWER_DIR)

clean:
	$(MAKE) -C $(PARSER_DIR) clean
	$(MAKE) -C $(SEMANTICS_DIR) clean
	$(MAKE) -C $(VIEWER_DIR) clean

