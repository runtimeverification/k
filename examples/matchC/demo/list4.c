#include <stdlib.h>
#include <stdio.h>

struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* reverse(struct listNode *x)
/*@ pre  <config><env> x |-> ?x </env> <heap> list(?x)(A), H </heap>
                 C </config> /\ true */
/*@ post <config><env> ?rho </env><heap> list(?x)(rev(A)), H </heap>
                 C </config> /\ returns(?x) */
{
  struct listNode *p;
  struct listNode *y;
  p = 0 ;
  /*@ invariant <config><env> p |-> ?p, x |-> ?x, y |-> ?y </env>
                        <heap> list(?p)(?B), list(?x)(?C), H </heap>
                        C </config> /\ rev(A) = rev(?C) @ ?B */
  while(x) {
    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }
  return p;
}


struct listNode* append(struct listNode *x, struct listNode *y)  
/*@ pre  <config><env> x |-> ?x, y |-> ?y  </env>
                 <heap> list(?x)(A), list(?y)(B), H </heap>
                 C </config> /\ true */
/*@ post <config><env> ?rho </env>
                 <heap> list(?x)(A @ B), H </heap> 
                 C </config> /\ returns(?x) */
{
  struct listNode *p;
  if (x == 0)
   return y;

  p = x;
  /*@ invariant <config><env> x |-> ?x, p |-> ?p, !rho </env>
                        <heap>
                          lseg(?x, ?p)(?A1),
                          ?p |-> ?v : listNode.val,
                          ?p + 1 |-> ?i : listNode.next,
                          list(?i)(?A2),
                          !H
                        </heap> 
                        C </config> /\ A = ?A1 @ [?v] @ ?A2 */
  while (p->next)
    p = p->next;
  p->next = y ;

  return x;
}


int length(struct listNode* x)
/*@ pre  <config><env> x |-> x0 </env>
                 <heap> list(x0)(A), H </heap> 
                 C </config> /\ true */
/*@ post <config><env> ?rho </env>
                 <heap> list(x0)(A), H </heap> 
                 C </config> /\ returns(len(A)) */
{
  int l;
  
  l = 0;
  /*@ invariant <config><env > x |-> ?x, l |-> len(?A1) </env>
                        <heap> lseg(x0,?x)(?A1), list(?x)(?A2), H </heap>
                        C </config > /\ A = ?A1 @ ?A2 */
  while (x) {
    l += 1;
    x = x->next ;
  }

  return l;
}


struct listNode* create(int n)
{
  struct listNode *x;
  struct listNode *y;
  x = 0;
  while (n)
  {
    y = x;
    x = (struct listNode*)malloc(sizeof(struct listNode));
    x->val = n;
    x->next = y;
    n -= 1;
  }
  return x;
}


void destroy(struct listNode* x)
{
  struct listNode *y;
  while(x)
  {
    y = x->next;
    free(x);
    x = y;
  }
}


void print(struct listNode* x)
{
  while(x)
  {
    printf("%d ",x->val);
    x = x->next;
  }
  printf("\n"); 
}


void f()
/*@ pre  <config><in> ListItem(n0), stream(S), SIn </in>
                 <out> SOut </out>
                 <heap> H </heap>
                 C </config> /\ len(S) = n0 */
/*@ pros <config><in> SIn </in>
                 <out> strem(rev(S)), SOut </out>
                 <heap> H </heap>
                 C </config> */
{
  int i; int n;
  struct listNode *x;  struct listNode *y;
  scanf("%d", &n);
  i = 0;  x = 0;
  /*@ inv <config><in> stream(?B), SIn </in>
                  <heap> list(x)(?A), H </heap>
                  !C1 </config>
                  /\ n = n0 /\ i <= n0 /\ len(?A) = i /\ rev(S) = rev(?B)@?A */
  while (i < n) {
    y = x;
    x = (struct listNode*)
        malloc(sizeof(struct listNode));
    scanf("%d", &(x->val));
    x->next = y;
    i += 1;
  }

  i = 0;
  /*@ inv <config><out> SOut, strem(?A) </out>
                  <heap> list(x)(?B), H </heap>
                  !C2 </config>
                  /\ n = n0 /\ i <= n0 /\ len(?A) = i /\ rev(S) = ?A@?B */
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
  struct listNode *x;
  struct listNode *y;
  x = create(5);
  /*@ assert <config><env> x |-> ?x, y |-> ?y </env>
                     <heap> list(?x)([1, 2, 3, 4, 5]) </heap> 
                     </config> /\ true */
  x = reverse(x);
  /*@ assert <config><env> x |-> ?x, y |-> ?y </env>
                     <heap> list(?x)([5, 4, 3, 2, 1]) </heap>
                     </config> /\ true */
  destroy(x);
  /*@ assert <config><env> x |-> ?x, y |-> ?y </env>
                    <heap> . </heap>
                    </config> /\ true */
  x = create(5);
  printf("x: ");
  print(x);
  /*@ assert <config><env > x |-> ?x, y |-> ?y </env>
                     <heap> list(?x)(!A) </heap>
                     </config> /\ true */
  x = reverse(x);
  printf("reverse(x): ");
  print(x);
  /*@ assert <config><env> x |-> ?x, y |-> ?y </env>
                     <heap> list(?x)(rev(!A)) </heap>
                     </config> /\ true */
  destroy(x);


  x = create(3);
  /*@ assert <config><env> x |-> ?x, y |-> ?y </env> 
                     <heap> list(?x)([1, 2, 3]) </heap> 
                     </config> /\ true */
  y = create(3);
  /*@ assert <config><env> x |-> ?x, y |-> ?y </env> 
                     <heap> list(?x)([1, 2, 3]), list(?y)([1, 2, 3]) </heap> 
                     </config> /\ true */
  x = append(x, y);
  /*@ assert <config><env> x |-> ?x, y |-> ?y </env> 
                     <heap> list(?x)([1, 2, 3, 1, 2, 3]) </heap> 
                     </config> /\ true */
  destroy(x);
  /*@ assert <config><env> x |-> ?x, y |-> ?y </env>
                     <heap> . </heap>
                     </config> /\ true */
  x = create(3);
  printf("x: ");
  print(x);
  /*@ assert <config><env> x |-> ?x, y |-> ?y </env> 
                     <heap> list(?x)(!A1) </heap> 
                     </config> /\ true */
  y = create(3);
  printf("y: "); 
  print(x);
  /*@ assert <config><env> x |-> ?x, y |-> ?y </env> 
                     <heap> list(?x)(!A1), list(?y)(!A2) </heap> 
                     </config> /\ true */
  x = append(x, y);
  printf("append(x, y): ");
  print(x);
  /*@ assert <config><env> x |-> ?x, y |-> ?y </env> 
                     <heap> list(?x)(!A1 @ !A2) </heap> 
                     </config> /\ true */
  destroy(x);

  f();
  return 0;
}


/*@ var ?x ?y ?p ?i ?v : ?Int */
/*@ var x0 : FreeInt */
/*@ var ?B ?C ?A1 ?A2 : ?Seq */
/*@ var !A !A1 !A2 : !Seq */
/*@ var A B : FreeSeq */
/*@ var ?rho ?H : ?MapItem */
/*@ var !rho !H : !MapItem */
/*@ var H : FreeMapItem */
/*@ var C : FreeBagItem */

