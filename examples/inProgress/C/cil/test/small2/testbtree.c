/***********************************************************************\
|									|
|	B+tree function tests						|
|									|
|									|
|	Jan Jannink	created 12/22/94	revised 1/30/95		|
|									|
\***********************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include "btree.h"


#ifdef _MSVC
 #define CLOCKS_PER_SEC 1000
 typedef long clock_t;
 clock_t __cdecl clock(void);
#else
 int clock(void);
#endif

#define TIMESTART(clk) {clk=(double)clock();}
#define TIMESTOP(clk)  {clk=1000000.0 * \
                            ((double)clock()-(clk))/CLOCKS_PER_SEC;}


int main(void)
{
  Tree	*Bplus;
  Nptr	keyNode;
  int	i, j;
  double clk;
  
  TIMESTART(clk);

  Bplus = initBtree(ARRAY_SIZE, MAX_FAN_OUT, compareKeys);
  for (i = 0; i < 20000; i++) {
    j = rand();
    if (search(Bplus, j) == NONODE) {
      insert(Bplus, j);
      //fprintf(stderr, "XXX %d, insert %d XXX\n", i, j);
    }
    else {
      delete(Bplus, j);
      //fprintf(stderr, "XXX %d, delete %d XXX\n", i, j);
    }
    // if (i > 2000) { listAllBtreeValues(Bplus); }
  }
  for (i = 0; i < 1505600; i++)
    (void) search(Bplus, i);
  // listAllBtreeValues(Bplus);
  freeBtree(Bplus);

  TIMESTOP(clk);
  printf("Run btreetest in %8.3lfms\n", clk / 1000.0);
  
  return 0;
}

