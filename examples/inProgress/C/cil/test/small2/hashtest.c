

/* A special purpose main */
#include "main.h"
#include "hash.h"
#include "alloc.h"

/* Some globals that PCC needs */
int error_level, anerror;
void myexit(int n) {
  exit(n);
}
#ifdef _MSVC
#define random rand
#else
/* extern int random(void); -- Weimer: not needed! */
#endif
int __mmId;
int debugMM;
int debug;


#pragma interceptCasts(on)

#ifndef ITERS
  #define ITERS 500000
#endif // ITERS

int main() {
  /* Test hash tables */
  PHASH h = NewHash();
  int i;
  double clk;
  int count = 0;
  int sz;
  //  int *foo, *foo1;
  
  /* Add and delete random numbers from the hash table */
  printf("inserting...\n");
  TIMESTART(clk);
  for(i=0;i<ITERS;i++) {
    int k = random() & 0x7FFFL;
    //    printf("inserting #%d\n", i);
//    if(i == 30000) {
//      foo = (int*) ((int) &main);  // Test scalar2pointer
//    }
    AddToHash(h, k, (void*)k);
  }

  // Now try to read from foo
  //  foo1 = foo + 1;
  //  i = *foo1;
  printf("finding...\n");
  for(i=0;i<ITERS;i++) {
    int k = random() & 0x7FFFL;
    void *data = NULL;
    if(HashLookup(h, k, & data)) {
      count ++;
    }
  }
  sz = SizeHash(h);
  
  printf("freeing...\n");
  FreeHash(h);
  TIMESTOP(clk);
  fprintf(stderr, "Hash has %d elements. Found %d times\n",
          sz, count);
  printf("Run hashtest in %8.3lfms\n", clk / 1000.0);
  fprintf(stderr, "Hello\n");
  exit (0);
  return 0;
}


