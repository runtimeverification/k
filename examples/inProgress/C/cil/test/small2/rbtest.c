

/* A special purpose main */
#include "main.h"
#include "redblack.h"
#include "alloc.h"

/* Some globals that PCC needs */
int error_level, anerror;
void myexit(int n) {
  exit(n);
}
#ifdef _MSVC
#define random rand
#else
/* weimer: not needed: extern int random(void); */
#endif
int __mmId;
int debugMM;
int debug;

// allow explicit call into gc
//int explicit_gc();


#define DATASIZE 16   // This is the size of the data that is reserved in
                      // each node

#ifndef ITERS
  #define ITERS 500000
#endif // ITERS

// had to make these global since spreading the functionality
// across several functions
int count = 0;
int sz;

void innerDoTreeStuff(int letGcFree)
{
  RBNode *t = NULL;
  int i;

  /* Add and delete random numbers from the hash table */
  printf("inserting...\n");
  for(i=0;i<ITERS;i++) {
    int k = random() & 0x7FFFL;
    insertRB(& t, k, DATASIZE);
  }
  printf("finding...\n");
  for(i=0;i<ITERS;i++) {
    int k = random() & 0x7FFFL;
    if(findRB(t, k)) {
      count ++;
    }
  }
  sz = 0;
  printf("sz++...\n");
  FORALLRBNODES(t, { sz ++; });

  if (!letGcFree) {
    // explicit freeing
    printf("freeing...\n");
    freeRB(t, NULL);
  }
  else {
    // will free a little further down, once the
    // stack is cleaner
  }
}

// this intermediate function serves to separate the computation,
// and its dirtying of the stack, from the gc which may follow
void doTreeStuff(int letGcFree)
{
  // cleanse the stack
  char buf[256];
  int i;

  for (i=0; i<256; i++) {
    buf[i] = 0;
  }

  innerDoTreeStuff(letGcFree);

  for (i=0; i<256; i++) {
    buf[i] = 0;
  }
}



int main(int argc /* char*argv[] */)  /* Drop this to avoid changing name*/
{
  /* Test hash tables */
  double clk;
  int letGcFree = (argc != 1);   // gc if any args
  RBNode *another = NULL;

  TIMESTART(clk);
  
  doTreeStuff(letGcFree);
  
  // another singleton tree to make the page not homogeneous
  insertRB(&another, 1, DATASIZE);

  if (letGcFree) {
    // use the gc
    printf("garbage collecting...\n");   
    
    // sm: I can't figure out why this won't work when
    // boxing is off.. it complains about explicit_gc_ (an
    // extra trailing underscore)..
    printf("# bytes freed: %d\n", 0);  //explicit_gc());
  }

  TIMESTOP(clk);

  fprintf(stderr, "Hash has %d elements. Found %d times\n",
          sz, count);
  printf("Run rbtest in %8.3fms\n", clk / 1000.0);
    // sm: removed 'l' in format string because gcc complains
  exit (0);
  return 0;
}


