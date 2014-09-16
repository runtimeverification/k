// Copyright (c) 2014 K Team. All Rights Reserved.
/*
 * Function that recursively transforms a binary tree into a singly linked list.
 * When freeing each tree node, it also prints its value.
 * Thus, the list of elements gets printed in reverse order.
 */


#include <stdlib.h>
#include <stdio.h>


struct treeNode {
  int value;
  struct treeNode *left;
  struct treeNode *right;
};

struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* tree_to_list_recursive(struct treeNode *t, struct listNode *l)
{
  struct listNode *ln;

  if (t == NULL)
    return l;

  ln = (struct listNode *) malloc(sizeof(struct listNode));
  ln->val = t->value;
  ln->next = tree_to_list_recursive(t->right, l);
  printf("%d ", t->value);
  l = tree_to_list_recursive(t->left, ln);
  free(t);

  return l;
}
