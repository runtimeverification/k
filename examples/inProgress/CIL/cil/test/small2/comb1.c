// comb1.c
// part 1/4 of a program expected to be combined

#ifndef __HEAPIFY
  #define __HEAPIFY
#endif

int global_com4; //even without an extern decl, this should link to comb4's 
                 //global var, which is initialized to 5.

int *globalPtr;

void hpfy()
{
  int local __HEAPIFY;
  globalPtr = &local;
}

int foo_com1(int x)
{
  return x + global_com4;
}
  
