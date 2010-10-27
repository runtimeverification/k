/*
 * This test is similar to 2003-05-26-Shorts.c except that it stores all
 * short values in a structure to test load and store operations on those
 * values.  It stresses masking and sign-extension for such load/stores.
 */
#include <stdio.h>
#include <stdlib.h>

typedef struct ShortsSet_struct {
  unsigned int   ui;
           int    i;
  unsigned short us;
           short  s;
  unsigned char  ub;
    signed char   b;
} ShortsSet;


/* Move the value here to prevent constant folding */
unsigned long long getL()
{
  return 0xafafafafc5c5b8a3ull;
}

int
main(int argc, char** argv)
{
  unsigned long long  UL = getL();      /* 0xafafafafc5c5b8a3 */
           long long   L = (long long) UL;

  ShortsSet* S = (ShortsSet*) malloc(sizeof(ShortsSet));
  S->ui = (unsigned int) UL;            /* 0xc5c5b8a3 =  3318069411 */
  S-> i =          (int) UL;            /* 0xc5c5b8a3 = -976897885 */

  S->us = (unsigned short) UL;          /*     0xb8a3 =  47267 */
  S-> s =          (short) UL;          /*     0xb8a3 = -18269 */

  S->ub = (unsigned char) UL;           /*       0xa3 =  163 */
  S-> b = (  signed char) UL;           /*       0xa3 = -93 */

  printf("   ui = %u (0x%x)\t\tUL-ui = %lld (0x%llx)\n",
         S->ui, S->ui, UL - S->ui, UL - S->ui);
  printf("ui*ui = %u (0x%x)\t  UL/ui = %lld (0x%llx)\n\n",
         (unsigned int) S->ui * S->ui, (unsigned int) S->ui * S->ui,
         UL/S->ui, UL/S->ui);

  printf("    i = %d (0x%x)\tL-i = %lld (0x%llx)\n",
         S->i, S->i, L - S->i, L - S->i);
  printf(" i* i = %d (0x%x)\tL/ i = %lld (0x%llx)\n\n",
         (int) S->i * S->i,  (int) S->i * S->i, L/S->i, L/S->i);

  printf("us    = %u (0x%x)\t\tUL-us = %lld (0x%llx)\n",
         S->us, S->us, UL - S->us, UL - S->us);
  printf("us*us = %u (0x%x)\t  UL/us = %lld (0x%llx)\n\n",
         (unsigned short) S->us * S->us, (unsigned short) S->us * S->us,
         UL/S->us, UL/S->us);

  printf(" s    = %d (0x%x)\tL-s = %lld (0x%llx)\n",
         S->s, S->s, L - S->s, L - S->s);
  printf(" s* s = %d (0x%x)\tL/ s = %lld (0x%llx)\n\n",
         (short) S->s * S->s, (short) S->s * S->s, L/S->s, L/S->s);

  printf("ub    = %u (0x%x)\t\tUL-ub = %lld (0x%llx)\n",
         S->ub, S->ub, UL - S->ub, UL - S->ub);
  printf("ub*ub = %u (0x%x)\t\tUL/ub = %lld (0x%llx)\n\n",
         (unsigned char) S->ub * S->ub, (unsigned char) S->ub * S->ub,
         UL/S->ub, UL/S->ub);

  printf(" b    = %d (0x%x)\t\tL-b = %lld (0x%llx)\n",
         S->b, S->b, L - S->b, L - S->b);
  printf(" b* b = %d (0x%x)\t\t\tL/b = %lld (0x%llx)\n\n",
         (signed char) S->b * S->b, (signed char) S->b * S->b, L/S->b, L/S->b);

  return 0;
}
