ML_ROOT_DIR = .

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

