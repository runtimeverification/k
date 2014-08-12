/*
 * Function list_read reads n elements from the standard input into a new
 * singly-linked list.
 */


#include <stdio.h>
#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* list_read(int n)
/*@ rule <k> $ => return ?x; ...</k> <heap>... . => list(?x)(A) ...</heap>
         <in> A => . ...</in>
    if n = len(A) */
{
  int i;
  struct listNode *x;
  struct listNode *p;

  if (n == 0)
    return NULL;

  x = (struct listNode*) malloc(sizeof(struct listNode));
  scanf("%d", &(x->val));
  x->next = NULL;

  i = 1;
  p = x;
  /*@ inv <heap>... lseg(x, p)(?B), p |-> [?v, 0] ...</heap> <in> ?C ...</in>
          /\ i <= n /\ len(?C) = n - i /\ A = ?B @ [?v] @ ?C */
  while (i < n) {
    p->next = (struct listNode*) malloc(sizeof(struct listNode));
    p = p->next;
    scanf("%d", &(p->val));
    p->next = NULL;
    i = i + 1;
  }

  return x;
}


//@ var v : Int
//@ var A, B, C : Seq

