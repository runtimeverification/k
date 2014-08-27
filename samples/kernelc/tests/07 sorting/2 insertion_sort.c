/*
 * Function that sorts the content of a singly linked list using insertion sort.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* insertion_sort(struct listNode* x)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)(A) => list(?x)(?A) ...</heap>
    if isSorted(?A) /\ seq2mset(A) = seq2mset(?A) */
{
  struct listNode* y;

  y = NULL;
  /*@ inv <heap>... list(y)(?B), list(x)(?C) ...</heap>
          /\ isSorted(?B) /\ seq2mset(A) = seq2mset(?B) U seq2mset(?C) */
  while (x != NULL) {
    struct listNode* n;

    n = x;
    x = x->next;
    n->next = NULL;
    if (y != NULL) {
      if (y->val < n->val) {
        struct listNode* z;

        z = y;
        /*@ inv <heap>... lseg(y,z)(?B), z |-> [?v,?n],
                          list(?n)(?C), n |-> [nval,0] ...</heap>
                /\ D = ?B @ [?v] @ ?C /\ ?v < nval */
        while (z->next != NULL && z->next->val < n->val)
          z = z->next;

        n->next = z->next;
        z->next = n;
      }
      else {
        n->next = y;
        y = n;
      }
    }
    else {
      y = n;
    }              
  }

  return y;
}


//@ var v, nval : Int
//@ var A, B, C, D : Seq
