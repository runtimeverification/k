// register an area, then clobber by calling fn

#include <stdio.h>     // printf
#include <stdlib.h>    // malloc

void clobber()
{                        
  printf("clobbering\n");
  
  // at the end we unregisterbelow, which will kill global/heap
  // areas since at the moment I fail to distinguish
}


int main()
{
  // make and register an area
  int *p = (int*)malloc(sizeof(*p));

  printf("printf result: %p\n", p);

  // clobber registration
  clobber();

  // try to use *p
  *p = 9;

  printf("worked ok!\n");

  return 0;
}

