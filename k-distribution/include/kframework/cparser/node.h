#ifndef NODE_H
#define NODE_H

#include <stdbool.h>
#include "parser.tab.h"

typedef struct node {
  char *symbol;
  char *sort;
  bool str;
  size_t nchildren;
  bool hasLocation;
  YYLTYPE location;
  struct node * children[];
} node;

typedef union value_type {
  char *token;
  node *nterm;
} value_type;

#endif
