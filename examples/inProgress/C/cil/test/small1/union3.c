#include "testharness.h"

#define offsetof(T, f) ((int)(& ((T*)0)->f))
#define printoffsetof(T, f, expected, err) \
   printf("Offset of " #f " in " #T " is %d. Expected %d\n", \
          offsetof(T, f), expected); \
   if(err && offsetof(T, f) != expected) E(err)

typedef union test {
  struct {
    int large[256];
  };
  int a;
  int b;
} TEST_UNION;

typedef struct tests {
  struct intests {
    int large[10];
    union intestsu {
      int i1; // The offset of this is 0 in GCC !!!
      int i2; // The offset of this is 0 in GCC
    }; // This is propagated as fields of struct tests
    int i3;
  };
  int a;
  union intestu { // This is a union. Its fields become fields of struct tests
    int u1, u2;
    struct {
      int f1, f2;
    };
  };
  int b;
} TEST_STRUCT;

int main() {
  TEST_STRUCT tests = { /* large[0] = */ 5 };

  // Even though the field is unnamed it does participate in initialization
  if(tests.large[0] != 5) E(1);

  printoffsetof(TEST_STRUCT, large, 0, 3);
  // There appears to be a bug in GCC. It thinks that fields i1 and i2 start
  // at offset 0 !!!
  printoffsetof(TEST_STRUCT, i1,   40, 4);
  printoffsetof(TEST_STRUCT, i2,   40, 5);

  printoffsetof(TEST_STRUCT, i3,   44, 6);
  printoffsetof(TEST_STRUCT, a,    48, 7);
  printoffsetof(TEST_STRUCT, u1,   52, 8);
  printoffsetof(TEST_STRUCT, u2,   52, 9);
  printoffsetof(TEST_STRUCT, f1,   52, 10);
  printoffsetof(TEST_STRUCT, f2,   56, 11);
  printoffsetof(TEST_STRUCT, b,    60, 12);

  
  SUCCESS; 
}

