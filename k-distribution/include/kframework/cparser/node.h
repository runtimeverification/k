#ifndef NODE_H
#define NODE_H

#include <stdbool.h>

typedef struct node {
  char *symbol;
  char *sort;
  bool str;
  size_t nchildren;
  struct node * children[];
} node;

typedef union value_type {
  char *token;
  node *nterm;
} value_type;

#endif
