/*
 * Function that sorts the content of a singly linked list using quicksort.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* append(struct listNode *x, struct listNode *y)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)(A), list(y)(B) => list(?x)(A @ B) ...</heap> */
{
  struct listNode *p;
  if (x == NULL)
    return y;

  p = x;
  /*@ inv <heap>... lseg(x, p)(?A1), list(p)(?A2) ...</heap> 
          /\ A = ?A1 @ ?A2 /\ ~(p = 0) */
  while (p->next != NULL)
    p = p->next;
  p->next = y;

  return x;
}


struct listNode* quicksort(struct listNode* x)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)(A) => list(?x)(?A) ...</heap>
    if isSorted(?A) /\ seq2mset(A) = seq2mset(?A) */
{
  struct listNode* p;
  struct listNode* y;
  struct listNode* z;

  if (x == NULL || x->next == NULL)
    return x;

  p = x;
  x = x->next;
  p->next = NULL;
  y = NULL;
  z = NULL;
  /*@ inv <heap>... p|->[v,0], list(x)(?A), list(y)(?B), list(z)(?C) ...</heap>
          /\ seq2mset(A) = {v} U seq2mset(?A) U seq2mset(?B) U seq2mset(?C)
          /\ leq(seq2mset(?B), {v}) /\ leq({v}, seq2mset(?C)) */
  while(x != NULL) {
    struct listNode* t;

    t = x;
    x = x->next;
    if (t->val < p->val) {
      t->next = y;
      y = t;
    }
    else {
      t->next = z;
      z = t;
    }
  }

  y = quicksort(y);
  z = quicksort(z);
  x = append(y, append(p, z));

  return x;
}


//@ var v : Int
//@ var A, B, C : Seq
