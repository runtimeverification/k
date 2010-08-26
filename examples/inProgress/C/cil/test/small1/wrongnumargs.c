#include <stdio.h>

void f(s1, s2) char *s1, *s2;
{
  printf(s1, s2);
}

int main(int argc, char** argv) {
  f("hello %S!\n", "wow");	  
  f("hello there: %s!\n", "wow");
  f("hello again!\n");
  return 0;
}

