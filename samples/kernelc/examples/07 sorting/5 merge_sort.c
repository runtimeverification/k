/*
 * Function that sorts the contents of a singly linked list using merge sort.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* merge_sort(struct listNode* x)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)(A) => list(?x)(?A) ...</heap>
    if isSorted(?A) /\ seq2mset(A) = seq2mset(?A) */
{
  struct listNode* p;
  struct listNode* y;
  struct listNode* z;

  if (x == NULL || x->next == NULL)
    return x;

  y = NULL;
  z = NULL;
  /*@ inv <heap>... list(x)(?A), list(y)(?B), list(z)(?C) ...</heap>
          /\ seq2mset(A) = seq2mset(?A) U seq2mset(?B) U seq2mset(?C)
          /\ (len(?B) = len(?C) \/ len(?B) = len(?C) + 1 /\ x = 0) */
  while (x != NULL) {
    struct listNode* t;

    t = x;
    x = x->next;
    t->next = y;
    y = t;

    if (x != NULL) {
      t = x;
      x = x->next;
      t->next = z;
      z = t;
    }
  }

  y = merge_sort(y);
  z = merge_sort(z);

  if (y->val < z->val) {
    x = y;
    p = y;
    y = y->next;
  }
  else {
    x = z;
    p = z;
    z = z->next;
  }
  /*@ inv <heap>...lseg(x,p)(?A1),p|->[?v,?n],list(y)(?B),list(z)(?C) ...</heap>
          /\ seq2mset(A) = seq2mset(?A1 @ [?v]) U seq2mset(?B) U seq2mset(?C)
          /\ leq(seq2mset(?A1 @ [?v]), seq2mset(?B))
          /\ leq(seq2mset(?A1 @ [?v]), seq2mset(?C))
          /\ isSorted(?A1 @ [?v]) /\ isSorted(?B) /\ isSorted(?C) */
  while (y != NULL && z != NULL) {
    if (y->val < z->val) {
      p->next = y;
      y = y->next;
    }
    else {
      p->next = z;
      z = z->next;
    }
		
    p = p->next;
  }
	
  if (y != NULL)
    p->next = y;
  else
    p->next = z;
	
  return x;
}


//@ var v, n : Int
//@ var A, B, C : Seq

