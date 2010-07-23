#include <stdlib.h>     // malloc

#define N 100000

struct S1 { struct T1* b; };
struct S2 { struct T2* b; };

struct T1 { int x; };
struct T2 { int x, y[N]; };

int main() {

   struct S1 *s1p;
   struct S2 *s2p;

   s2p = (struct S2*)malloc(sizeof(struct S2));

   s1p = (struct S1*) s2p;

   s1p->b = (struct T1*)malloc(sizeof(struct T1));
   //s2p->b = (struct T2*)(s1p->b);

   s2p->b->x = 1;

   /* if N is large enough, this should segfault */
   s2p->b->y[N-1] = 3;

   return 0;

}
