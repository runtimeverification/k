/* Tests for checking the return values */
#include "../small1/testharness.h"

TESTDEF succ : success

struct str1 {
  int  x1;
  int *x2;
  struct {
    int i1;
    int *i2;
  } x3;
};

int global;

struct str1 retstr() {
  int local;
  struct str1 res = { 0, &global, 1, &global }; // KEEP : error
  struct str1 res = { 0, &local, 1, &global }; // KEEP : error = Returning a local
  struct str1 res = { 0, &global, 1, &local }; // KEEP : error = Returning a local
  return res;
}

struct strarr {
  int i1;
  int *a[7];
};

struct strarr retarr() {
  int local;
  struct strarr res = { 0, &global, &global, &global }; // KEEP : error=Error 3
  struct strarr res = { 0, &global, &local, &global }; // KEEP : error=Returning a local
  return res;
}

union unfoo {
  struct { int *e1; int *e2; int *e3; int *e4; } f1;
  int *f2[4];
};

union unfoo retunion() {
  int local;
  union unfoo res = { &global, &local, &global }; // KEEP : error =Returning a local
  return res;
}

union unempty { } retunempty() {
  union unempty res;
  return res;
}

int main() {
  retstr();
  retarr();
  retunion();
  retunempty(); E(6);// KEEP : error = Error 6

  E(3); // ERROR(3)
  SUCCESS;
}
