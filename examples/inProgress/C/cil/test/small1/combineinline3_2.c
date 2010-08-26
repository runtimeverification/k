
int bar(int x); /* Declare it here. Name does not matter. */

inline int bar(int x) { return x; } 


int getfoo2() {
  return (int)bar;
}
