#include <stdio.h>

int main(int argc, char** argv) {

  int (* badfunc) ();

  badfunc = puts;

  (*badfunc)("hello, nice to meet you.");
  
  return 0;
}
