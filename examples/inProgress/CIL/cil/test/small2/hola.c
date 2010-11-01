// hola.c
// tiny program for scott's testing purposes

#include <stdio.h>     // printf
#include <stdlib.h>    // malloc

#if 1
// this is a pointer in the global area
int *globalPtr;

// here is a global integer to point at
int globalInt = 5;


// something so I can tell one section from another
void separator() {}


// explicitly declare the entry to the gc
void GC_gcollect(void);


// wtf?
int LibTkn;
int LibTkn010;


int main()
{
  // here's a local int to point at
  int localInt;

  // point at them
  globalPtr = &globalInt;

  separator();

  // this simply isn't allowed!
  //globalPtr = &localInt;

  separator();

  globalPtr = (int*)malloc(sizeof(int));

    
  // allocate lots of memory which will all be unreachable,
  // in hopes of triggering the GC
  {
    int i;
    void **p, ***q;
    for (i=0; i<1000; i++) {
      p = (void**)malloc(sizeof(*p));
      *p = (void*)5;
      // **((int**)p) = 7;
    }
  }

  // now will the gc be called?
  // (requires BOX=1 so we get safec{debug,}lib.a ...)
  //GC_gcollect();

  printf("hola finished successfully\n");
  return 0;


  #if 0
  int x,y;
  x = printf("hola senior.\n");
  x += printf("what is ascii for accented o and tilde n?\n");
  x++;
  printf("x = %d\n", x);
  y = printf("hmm\n");
  return x?0:x;
  #endif // 0
}
#endif // 0
