// Copyright (c) 2014 K Team. All Rights Reserved.
#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int value;
  struct listNode *next;
};


int main()
{
  struct listNode *x;

  x = (struct listNode*) malloc(sizeof(struct listNode));
  printf("%d\n", x->value);

  return 0;
}

