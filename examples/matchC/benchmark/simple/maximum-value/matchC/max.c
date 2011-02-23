#include <stdlib.h>

int max(int x, int y)
// pre x = x0 /\ y = y0
// post returns(max-val(x0 , y0))
{
  int z;
  if (x < y) z = y;
  else z = x;
  return z;
}

int main()
{
  int x;
  int y;
  x = 8;
  y = 45;
  x = max(x,y);
  printf("The maximum value between 8 and 45 is: %d\n", x);;
  //@ assert <out> [45] </out>
  return 0;
}

