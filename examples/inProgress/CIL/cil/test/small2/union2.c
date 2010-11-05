#include "../small1/testharness.h"
#include "../small1/testkinds.h"

// NUMERRORS 12

union unsafeu1 { 
    int *f1;
    int *f2[2];
    struct { int *a1, a2, *a3; } f3;
    /* unsafe union: a2 and f2[1] */
} * x;

union unsafeu2 { 
    int *g1;
    struct { int *b1, b2; } g2; 
    struct { int *c1, *c2, *c3; } g3;
    /* unsafe union: c2 and b2 */
} * y;

union safeu {
  int a[2];
  char b[8]; 
  // safe union: all scalars
} * z; 

union safeu2 {
  struct { int a; int *b; } s1;
  struct { int c; int *d; } s2; 
} same, *sptr; 


int main() {
  if(HAS_KIND(x->f1, WILD_KIND)) E(1); //ERROR(1):Error 1
  // x will be SAFE because it is not used at all to access the fields
  if(HAS_KIND(x, SAFE_KIND)) E(12); //ERROR(12):Error 12
  if(HAS_KIND(y->g1, WILD_KIND)) E(2); //ERROR(2):Error 2
  if(HAS_KIND(z, SAFE_KIND)) E(3); //ERROR(3):Error 3
#if ERROR == 4
  sptr = &same; 
  sptr->s1.b++;
  if(HAS_KIND(sptr->s2.d, FSEQ_KIND)) E(4); //ERROR(4):Error 4
#endif
#if ERROR == 5
  sptr = &same; 
  sptr->s2.d--;
  if(HAS_KIND(sptr->s1.b, SEQ_KIND)) E(5); //ERROR(5):Error 5
#endif
#if ERROR == 6
  sptr = &same; 
  y = sptr->s2.d; // makes things WILD
  if(HAS_KIND(sptr->s1.b, WILD_KIND)) E(6); //ERROR(6):Error 6
#endif
#if ERROR == 7
  sptr = &same; 
  y = sptr->s1.b; // makes things WILD
  if(HAS_KIND(sptr, SAFE_KIND)) E(7); //ERROR(7):Error 7
#endif
  {
    // These two unions should be fine
    union { 
      struct { int a; int b; int c; } one;
      struct { int p; int q; int r; int *s; } two; 
    } *aa;
    union { 
      struct { int a; int b; } one;
      struct { int p; int q; int *s; } two; 
    } *bb;
#if ERROR == 8
    aa = bb; 
    if(HAS_KIND(aa, WILD_KIND)) E(8); //ERROR(8):Error 8
#endif
#if ERROR == 9
    bb = aa; 
    if(HAS_KIND(aa, WILD_KIND)) E(9); //ERROR(9):Error 9
#endif
  }
  {
    // These two unions should be fine
    union ulong { 
      struct { int a; int b; int c; } one;
      struct { int p; int q; int r; int s; } two; 
    } adata, *aa = &adata;
    union ushort { 
      struct { int a; int b; } one;
      struct { int p; int q; int s; } two; 
    } bdata, *bb = &bdata;
#if ERROR == 10
    // Since aa is longer, the bb will have to be FSEQ to be able to check the
    // length
    aa = bb; //ERROR(10):Failure UBOUND
#endif
#if ERROR == 11
    bb = aa; 
    if(HAS_KIND(aa, SAFE_KIND)) E(11); //ERROR(11):Error 11
#endif
  }
  SUCCESS;
}
