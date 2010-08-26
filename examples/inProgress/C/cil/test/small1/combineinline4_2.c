
int bar(int x); /* Declare it here. Name does not matter. */


int getfoo2() { /* Use bar before definition */
  return (int)bar;
}


inline int bar(int x) { return x; } 

