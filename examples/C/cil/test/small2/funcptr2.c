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

struct Func {
  struct S* (*returnsS)(int a);
};

struct Func *makeFunc(struct S* (*func)())
{
  struct Func *f = (struct Func*)malloc(sizeof(*f));
  f->returnsS = func;
  return f;
}

struct S* makeAnS(int a)
{
  struct S *ret = (struct S*)malloc(sizeof(*ret));
  ret->ix = a;
  ret->py = NULL;
  printf("returning %p\n", ret);
  return ret;
}

int zero = 0;

int doSomethingToS(struct Func *func, int a)
{
  struct S *wildptr;

  wildptr = (*(func->returnsS))(a);

  printf("got back %p\n", wildptr);

  // make wildptr be wild
  if (zero) {   
    struct T *pt = (struct T*)malloc(sizeof(*pt));
    pt->px = (int*)malloc(sizeof(* (pt->px) ));
    *(pt->px) = 3;
    pt->iy = 13;

    wildptr = (struct S*)pt;
  }

  return 0;
}

struct Func f;

int main()
{
  return doSomethingToS(makeFunc(makeAnS), 4);
  //                             ^^^^^^^
  // this argument is the wrong type, but silently accepted!
}
