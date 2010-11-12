///////////////////////////////////////////////
// Example illustrates the use of tagged unions
// and types
//////////////////////////////////////////////
#include "../../../include/havoc.h"
#include <malloc.h>


typedef struct _A{
  int a;
  int *b;
}A, *PA;

typedef struct _B{
  char *c;
  struct _A d;
  int *e;
} B, *PB, **PPB;

typedef union _C{
  struct _A f;
  struct _B g;
}C, *PC;

typedef struct _D{
  int *i;
  int tag;      //tag for the union
  union _C k;
}D, *PD;
  
__declare_havoc_bvar_type(_H_x, PD);

#define __union_inv(tag,y)  (y != 0 && \
                             (tag == 1 ==> __type(y, PA)) && \
			     (tag == 2 ==> __type(y, PB)))

#define __union_type_inv_D  __forall(_H_x, __values(PD), \
                                        _H_x == 0 || __union_inv(_H_x->tag, &_H_x->k))


//////////////////////////////////////////
// type invariant to express tagged union
__requires (__union_type_inv_D)
__ensures  (__union_type_inv_D)
__instrument_universal_all
void __instrument_union_type_inv();
/////////////////////////////////////////

__requires (x != 0)
int* P(PD x)
{
  if (x->tag == 1)
    return x->k.f.b;
  if (x->tag == 2)
    return x->k.g.e; 
  return 0;
}

__requires (x != 0)
PA Q(PD x)
{
  if (x->tag == 1)
    return &x->k.f;
  if (x->tag == 2)
    return &x->k.g.d;
  return 0;
}

__modifies (&((PD)__return)->tag)
__modifies (&((PD)__return)->k.f.b)
__modifies (&((PD)__return)->k.g.e)
PD R(int flag, int* y)
{  
  PD x = (PD) malloc(sizeof(D));

  if (flag)
    {
      __hv_assume(x->tag == 1);
      x->tag = 1;
      x->k.f.b = y;      
    }
  else
    {
      __hv_assume(x->tag == 2);
      x->tag = 2;
      x->k.g.e = y;
    }
  
  return x;
}
