ML_ROOT_DIR = .

PARSER_DIR = $(ML_ROOT_DIR)/parser
PARSER_JAR = $(PARSER_DIR)/matchCparser.jar
SEMANTICS_DIR = $(ML_ROOT_DIR)/semantics
SEMANTICS_COMPILED = $(SEMANTICS_DIR)/matchC-compiled.maude
VIEWER_DIR = $(ML_ROOT_DIR)/viewer
VIEWER_JAR = $(VIEWER_DIR)/matchCViewer.jar
BIN_DIR = $(ML_ROOT_DIR)/bin


all:  build

build:
	$(MAKE) -C $(PARSER_DIR)
	$(MAKE) -C $(SEMANTICS_DIR)
	$(MAKE) -C $(VIEWER_DIR)

install: build
	cp $(PARSER_JAR) $(BIN_DIR)
	cp $(SEMANTICS_COMPILED) $(BIN_DIR)
	cp $(VIEWER_JAR) $(BIN_DIR)

clean:
	$(MAKE) -C $(PARSER_DIR) clean
	$(MAKE) -C $(SEMANTICS_DIR) clean
	$(MAKE) -C $(VIEWER_DIR) clean

