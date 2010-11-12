#include "../../../include/havoc.h"

typedef struct _A{
  int a;
  int *b;
}A, *PA;

typedef struct _B{
  struct _A c;
  int d;
} B, *PB;

typedef struct _C{
  int e;
  int *f;
  int g;
  struct _A i;
} C, *PC;

__requires (__type(x, PA))
void P0(void* x){
  PA y = (PA)x;
}

__instrument_field_equiv(
      __field_equiv(__field(A*, a), __field(C*,e))
      __field_equiv(__field(A*, b), __field(C*,f))
      __type_equiv(__field(C*, g))
)


__requires (x != 0)
__modifies (&x->c.a)
void P1(PB x){
  PA y = (PA)x; // this is typesafe as B is a structural subtype of A
  y->a = 10;
}

__requires (x != 0)
PA Q1_good(PC x){ // add offset of field i in struct C
  return (PA) ((char *)x + 12); 
}

__requires (x != 0)
PA Q1_bad(PC x){
	return (PA) (((char*)x) + 16); // does not type check

}

__requires (x != 0)
__modifies (&x->e)
__ensures  (x->e == 10)
void P2(PC x){
  PA y = (PA)x; //type safety violation unless havoc is informed 
    //of physical subtyping
  y->a = 10;
}

__requires (x != 0)
__modifies (x)
void P3(int *x)
{
  (*x)++;
}

__requires (x != 0)
__requires (&x->g != 0)
__modifies (&x->g)
void P4(PC x)
{
  P3((int *)&x->g); //type safety violation unless __type_equiv is specified
}

