/*
 * Function that recursively transforms a binary tree into a singly linked list.
 * When freeing each tree node, it also prints its value.
 * Thus, the list of elements gets printed in reverse order.
 */


#include <stdlib.h>
#include <stdio.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};

struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* tree_to_list_recursive(struct treeNode *t, struct listNode *l)
/*@ rule <k> $ => return ?l; ...</k>
         <heap>... tree(t)(T),list(l)(A) => list(?l)(tree2list(T) @ A) ...</heap>
         <out>... . => rev(tree2list(T)) </out> */
{
  struct listNode *ln;

  if (t == NULL)
    return l;

  ln = (struct listNode *) malloc(sizeof(struct listNode));
  ln->val = t->val;
  ln->next = tree_to_list_recursive(t->right, l);
  printf("%d ", t->val);
  l = tree_to_list_recursive(t->left, ln);
  free(t);

  return l;
}


//@ var A : Seq
//@ var T : Tree

