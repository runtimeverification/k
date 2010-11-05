// testing function ptrs etc

#include <stdlib.h>     // malloc/free
#include <stdio.h>      // printf

struct S {
  int ix;
  int *py;
};

// gratuitously incompatible with S
struct T {
  int *px;
  int iy;
};

typedef int (*acceptsS)(struct S *ps, int a);

int multXbyY(struct S *ps, int a)
{
  printf("in multXbyY, a is %d\n", a);
  return ps->ix * (* (ps->py) ) + a;
}

int zero = 0;    // hide a literal from CCured

int doSomethingToS(struct S *ps, acceptsS func)
{
  struct S *wildptr = ps;

  printf("in doSomethingToS\n");

  // make wildptr be wild
  if (zero) {
    struct T *pt = (struct T*)malloc(sizeof(*pt));
    pt->px = (int*)malloc(sizeof(* (pt->px) ));
    *(pt->px) = 3;
    pt->iy = 13;

    wildptr = (struct S*)pt;
  }

  // wildptr is wild, and func's type has been changed to appear
  // to accept a wild pointer, but it still points to 'multXbyY',
  // which has been inferred to accept a safe ptr; therefore, instead
  // of '9' being passed as the 2nd arg, 'multXbyY' sees wildptr's _b
  // field as its 'a' arg
  printf("calling func with a=%d\n", 9);
  return func(wildptr, 9);
}

int main()
{
  struct S *ps = (struct S*)malloc(sizeof(*ps));
  int ret;

  ps->ix = 8;
  ps->py = (int*)malloc(sizeof(* (ps->py) ));
  *(ps->py) = 9;
  ret = doSomethingToS(ps, multXbyY) - 81;

  free(ps);

  printf("returning %d from main\n", ret);
  return ret;
}
