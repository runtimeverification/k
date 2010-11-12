////////////////////////////////////////
// Example with type invariant and arrays
////////////////////////////////////////

#include "../../../include/havoc.h"
#include <malloc.h>

typedef struct _Foo{
  char *buf; /* char buffer */
  int  len;  /* length of the buffer */
} Foo, *PFoo;

typedef char *PCHAR;

__declare_havoc_bvar_type(_H_x, PFoo);
__declare_havoc_bvar_type(_H_y, char*);

#define __char_array(x, n)       __array(x, sizeof(char), n)
#define __buf_array(x)           __char_array(x->buf, x->len)
#define __buf_len_inv_Foo(x)     __forall(_H_y, __buf_array(x), _H_y != 0 && __type(_H_y, PCHAR))
#define __type_inv_Foo           __forall(_H_x, __values(PFoo), _H_x == 0 || _H_x->len == -1 || __buf_len_inv_Foo(_H_x))

////////// Instrument type invariant ////////////
__requires(__type_inv_Foo)
__ensures (__type_inv_Foo)
__instrument_universal_all
void __instrument_type_invariant_Foo();
/////////////////////////////////////////////////

__modifies (&x->len)
__modifies (&x->buf)
void Alloc(PFoo x)
{
  if (!x) 
    return;

  x->buf = (char *) malloc (sizeof(char) * 10);
  x->len = 10;
}

__ensures  (x == 0 || __forall(_H_y, __buf_array(x), *_H_y == y))
__modifies (__old(__buf_array(x)))
void Init(PFoo x, char y) 
{
  int i = 0;

  if (!x) 
    return;
  
  if (x->len <= 0)
    return;

  __loop_invariant(
		   __loop_assert   (__forall(_H_y, __char_array(x->buf, i), *_H_y == y))
		   __loop_modifies (__old(__buf_array(x)))
		   )
  while (i < x->len)
    {
      x->buf[i] = y;
    }
  
}

__requires  (x == 0 || __forall(_H_y, __buf_array(x), *_H_y == y))
void Access(PFoo x, char y)
{
  int i = 0;

  if (!x) 
    return;

  if (x->len <= 0)
    return;


  while (i < x->len)
    {
       __hv_assert(x->buf[i] == y);
    }
  
}


PFoo g;

__modifies (&g)
     __modifies (&g->len)
      __modifies (&g->buf)
     __modifies (__buf_array(g))
void Entry()
{
  g = (PFoo) malloc(sizeof(Foo));
  
  g->len = -1;

  Alloc(g);

  Init(g, 'a');

  Access(g, 'a');

}


