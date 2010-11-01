
// A CIL test.  But use CCured on it for stricter checking of the foo2 case.

int z;
typedef struct bar { int* ip; } Bar;
Bar global = {0};

int foo (int x) {
  switch (x) {
  case 0:
    x++;
    z++;
    break;
  default:
    return z;
  }
  // we need a return here.  Make sure there's a warning if it's missing.
  return z; //DROP switch: success = Warning: Body of function foo falls-through
}

Bar foo2 (int x) {
  while (1) {
    if (z++)
      return global;
  }
  // no need for a return here. If CIL falsely assumes we need a return,
  // ccured will fail to compile since it doesn't know how to make a Bar.
}

Bar foo3 (int x) {
  while (z < 10) {
    z++;
  }
  // we need this return.
  return global; //DROP loop: error
}

int main(){
  return 0;
}
