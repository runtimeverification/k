#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "node.h"
#include "parser.tab.h"
#include "scanner.h"

static void append(char *buf, size_t *bufidx, char *str, size_t len) {
  memcpy(buf+*bufidx, str, len);
  *bufidx = *bufidx + len;
}

char *enquote(char *str) {
  size_t len = strlen(str);
  size_t bufidx = 1;
  char *res = malloc(len*4+3);
  res[0] = '"';
  for(int idx = 0; idx < len; idx++) {
    char c = str[idx];
    switch (c) {
      case '"':  append(res, &bufidx, "\\\"", 2); break;
      case '\\': append(res, &bufidx, "\\\\", 2); break;
      case '\n': append(res, &bufidx, "\\n", 2);  break;
      case '\t': append(res, &bufidx, "\\t", 2);  break;
      case '\r': append(res, &bufidx, "\\r", 2);  break;
      default:
        if (c >= 32 && c < 127) {
          append(res, &bufidx, &c, 1);
        } else {
          char buf[5];
          sprintf(buf, "\\x%02hhx", (unsigned char)c);
          append(res, &bufidx, buf, 4);
        }
    }
  }
  append(res, &bufidx, "\"", 2);
  return res;
}

static bool equalsSymbol(node *x0, node *x1) {
  return strcmp(x0->symbol, x1->symbol) == 0;
}

bool equalsNode(node *x0, node *x1) {
  if (x0->str != x1->str) {
    return false;
  }
  if (x0->str) {
    return strcmp(x0->symbol, x1->symbol) == 0;
  } else {
    if (!(equalsSymbol(x0, x1) && x0->nchildren == x1->nchildren)) {
      return false;
    }
    for (size_t i = 0; i < x0->nchildren; i++) {
      if (!equalsNode(x0->children[i], x1->children[i])) {
        return false;
      }
    }
    return true;
  }
}

char *injSymbol(char *lesser, char *greater) {
  char *prefix = "inj{";
  char *infix = ", ";
  char *suffix = "}";
  size_t len = strlen(prefix) + strlen(suffix) + strlen(lesser) + strlen(greater) + strlen(infix) + 1;
  char *symbol = malloc(len);
  strcpy(symbol, prefix);
  strcat(symbol, lesser);
  strcat(symbol, infix);
  strcat(symbol, greater);
  strcat(symbol, suffix);
  return symbol;
}

YYSTYPE mergeAmb(YYSTYPE x0, YYSTYPE x1) {
  if (equalsNode(x0.nterm, x1.nterm)) {
    return x0;
  }
  node *n = malloc(sizeof(node) + sizeof(node *) * 2);
  node *x0n = x0.nterm;
  node *x1n = x1.nterm;
  char *prefix = "Lblamb{";
  char *suffix = "}";
  size_t len = strlen(prefix) + strlen(suffix) + strlen(x0n->sort) + 1;
  char *symbol = malloc(len);
  strcpy(symbol, prefix);
  strcat(symbol, x0n->sort);
  strcat(symbol, suffix);
  n->location = x0n->location;
  n->hasLocation = false;
  n->symbol = symbol;
  n->sort = x0n->sort;
  n->str = false;
  n->nchildren = 2;
  n->children[0] = x0n;
  n->children[1] = x1n;
  YYSTYPE result = {.nterm = n};
  return result;
}

void print(node *current) {
  if (current->hasLocation) {
    printf("Lbl'Hash'location{");
    printf("%s", current->sort);
    printf("}(");
  }
  printf("%s", current->symbol);
  if (!current->str) {
    printf("(");
    for (int i = 0; i < current->nchildren; i++) {
      node *child = current->children[i];
      print(child);
      if (i != current->nchildren - 1) printf(",");
    }
    printf(")");
  }
  if (current->hasLocation) {
    printf(", \\dv{SortString{}}(%s), \\dv{SortInt{}}(\"%d\"), \\dv{SortInt{}}(\"%d\"), \\dv{SortInt{}}(\"%d\"), \\dv{SortInt{}}(\"%d\"))", enquote(current->location.filename), current->location.first_line, current->location.first_column, current->location.last_line, current->location.last_column);
  }
}

extern node *result;
extern char *filename;

int main(int argc, char **argv) {
  yyscan_t scanner;
  yylex_init(&scanner); 
  if (argc < 2 || argc > 3) {
    fprintf(stderr, "usage: %s <file> [<filename>]\n", argv[0]);
    exit(1);
  }
  if (argc == 3) {
    filename=argv[2];
  } else {
    filename=argv[1];
  }
  FILE *f = fopen(argv[1], "r");
  if (!f) {
    int len = strlen(argv[0]) + strlen(argv[1]) + 19;
    char *buf = malloc(len);
    snprintf(buf, len, "%s: cannot access '%s'", argv[0], argv[1]);
    perror(buf);
    exit(1);
  }
  yyset_in(f, scanner);
  int status = yyparse(scanner);
  if (status) {
    exit(status);
  }
  print(result);
  printf("\n");
  yylex_destroy(scanner);
}
