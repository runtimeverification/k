// trivial-tb.c
// NUMERRORS 4
// test the test-bad target and lib/test-bad script

#include <stdio.h>           // printf
#include <stdlib.h>          // exit

void fail(int val)
{
  printf("fail(%d)\n", val);
  exit(val);
}

int main()
{
  fail(1);        // ERROR(1)
  fail(2);        // ERROR(2)
  fail(3);        // ERROR(3)
  fail(4);        // ERROR(4)

  printf("no failure\n");
  return 0;
}


