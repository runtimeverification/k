#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


void readWrite()
//@ pre  <in> [n0] @ A @ I </in><out> O </out> /\ len(A) = n0
//@ post <in> I </in><out> O @ rev(A) </out>
{
  int i;
  int n;
  struct listNode *x;
  struct listNode *y;

  scanf("%d", &n);

  i = 0;
  x = 0;
  /*@ invariant <in> ?B @ I </in><heap> list(x)(?A), !H </heap>
                /\ n = n0 /\ i <= n /\ len(?B) = n - i /\ A = rev(?A) @ ?B */
  while (i < n) {
    y = x;
    x = (struct listNode*) malloc(sizeof(struct listNode));
    scanf("%d", &(x->val));
    x->next = y;
    i += 1;
  }

  i = 0;
  /*@ invariant <out> O @ ?A </out><heap> list(x)(?B), !H </heap>
                /\ n = n0 /\ i <= n /\ len(?B) = n - i /\ A = rev(?A @ ?B) */
  while (i < n) {
    y = x->next;
    printf("%d ",x->val);
    free(x);
    x = y;
    i += 1;
  }
}


int main()
{
  /* la verificare preconditiei functiei readWrite, trebui rezolvata implicatia
   * true ===> [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] === !A @ !I /\ len(!A) = 10
   * implicatia are solutia triviala !A e tot si fameul !I e nimic
   * dar nu vad o methoda usoara pentru prover
   * fara aceasta implicatie functia nu poate fi chemata din main
   */  
  //@ assume <in> [10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] </in><out> epsilon </out>
  readWrite();
  //@ assert <in> epsilon </in><out> [10, 9, 8, 7, 6, 5, 4, 3, 2, 1] </out>

  return 0;
}


//@ var A, B, I, O : Seq
//@ var !H : !MapItem

