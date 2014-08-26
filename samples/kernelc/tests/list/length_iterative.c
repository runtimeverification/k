// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function length_iterative returns the length of a singly linked list.
 * The length is iteratively computed.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


int length_iterative(struct listNode* x)
{
  int y;

  y = 0;
  while (x != NULL) {
    y = y + 1;
    x = x->next;
  }

  return y;
}
