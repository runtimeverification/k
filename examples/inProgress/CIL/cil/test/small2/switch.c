#include "../small1/testharness.h"

//the file should compile without changes.
TESTDEF baseline: success

// Testing some ugly switch cases
int foo(int x, int y) {
  switch(x) {
    y = "who runs this?"[3];
    exit(1);
  default:
  default:                      //KEEP dupDefault1: error = duplicate default
    y ++;
    goto L1;
  case 1:
  L2:
  case 20:
    y ++;
    break;
    y ++;
  L1:
    if(y > 5) {
    case 7:
      x ++;
    } else {
      while(x < 33) {
      default:                 //KEEP dupDefault2: error = duplicate default
      case 9:
        x ++;
        break;
      }
      break;
    }

    goto L2;
  }
  if(x < 30)
    goto L1;
  return x + y;
}

//braces aren't required.
// (the two cases and the return are in the same statement.)
int bar(int i) {
   switch (i)
     case 0:
     case 1:
     return i;
   return 0;
}

int main() {
  int one = bar(1) + bar(2);
  int res =
    one +
    foo(1, 2) +
    17 * foo(9, 5) +
    126 * foo(7, 2) +
    3037 * foo(15, 9);
  printf("Result is: %d\n", res);
  if(res != 171822)
    exit(1);
  return 0;
}
