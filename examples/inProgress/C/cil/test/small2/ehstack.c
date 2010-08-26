// ehstack.c
// NUMERRORS 1
// build a small exception-handling stack, verify field annotation works

#ifndef CCURED
  #define __MAYPOINTTOSTACK
#endif

struct Entry {
  struct Entry *next __MAYPOINTTOSTACK;
  int *otherPointer;     // not allowed to point at stack
  int x;
};

int *somePtr;

//matth: making e1 global so ERROR(1) below fails.
struct Entry e1;

int function(int argc, char **argv)
{
  //matth: if e1 is local, there's nothing wrong with storing &e2.x in it.
  struct Entry /*e1,*/ e2; 
  int *wildGuy;

  // make everybody wild
  wildGuy = (int*)&somePtr;
  wildGuy = (int*)&e1;
  wildGuy = (int*)&e2;

  // I want to allow this
  e1.next = &e2;

  // but not this
  e1.otherPointer = &e2.x;      // ERROR(1): Storing stack address

  return 0;
}


int main(int argc, char **argv) {
  function(argc, argv);
}
