// baddef2.c: other def'n
  
#include <stdio.h>

struct S {
  int x;
  int y;
  int z;      // third field!
};

int size2() { return sizeof(struct S); }
int size1();  // from baddef1

int main()
{
  int s1, s2;

  printf("size1: %d\n", s1=size1());
  printf("size2: %d\n", s2=size2());
  printf("(correct output is 8, then 12)\n");
  
  if (s1==8 && s2==12) {
    return 0;
  }
  else {
    return 2;
  }
}


