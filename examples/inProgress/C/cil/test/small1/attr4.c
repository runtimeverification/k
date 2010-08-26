#include "testharness.h"

typedef struct {
  int f1;
  char f1pad;
  int f2  __attribute__((packed)), f3 __attribute__((packed));
  char f2pad;
  int f4, f5 __attribute__((packed)); // Only f5 is packed
  char f3pad;
  int __attribute__((packed)) f6, f7; // Both f6 and f7 are packed
} STR;


#define offsetof(f,t) ((int)(&((t*)(0))->f))


int main() {
  printf("Offset 1 = %d\n", offsetof(f1, STR));
  printf("Offset 2 = %d\n", offsetof(f2, STR));
  printf("Offset 3 = %d\n", offsetof(f3, STR));
  printf("Offset 4 = %d\n", offsetof(f4, STR));
  printf("Offset 5 = %d\n", offsetof(f5, STR));
  printf("Offset 6 = %d\n", offsetof(f6, STR));
  printf("Offset 7 = %d\n", offsetof(f7, STR));

  if(offsetof(f1, STR) != 0 ||
     offsetof(f2, STR) != 5 ||
     offsetof(f3, STR) != 9 ||
     offsetof(f4, STR) != 16 ||
     offsetof(f5, STR) != 20 ||
     offsetof(f6, STR) != 25 ||
     offsetof(f7, STR) != 29) {
    return 1;
  }

  return 0;
}
