#ifndef NODE_H
#define NODE_H

#include <stdbool.h>

typedef struct node {
  char *symbol;
  bool str;
  size_t nchildren;
  struct node * children[];
} node;

#endif
