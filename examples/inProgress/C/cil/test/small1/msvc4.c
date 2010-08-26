#include "testharness.h"

// This requires VC.NET

// It does not matter where we put the declspec 
__declspec(align(16)) struct foo {
  int x1;
} g; // Only g is aligned


typedef struct __declspec(align(8)) _DEVICE_OBJECT {
  int x1;
} DEVICE_OBJECT;


int main() {
  struct _DEVICE_OBJECT x; // Inherits the alignment
  struct {
    int a;
    // 4 bytes Padding
    struct _DEVICE_OBJECT x;
  } y;
  
  struct {
    int a;
    struct foo b; // No padding
  } z;
  
  if(sizeof(x) != 8) {
    printf("sizeof(DEVICE_OBJECT) = %d\n", sizeof(DEVICE_OBJECT));
    E(1);
  }

  if(sizeof(y) != 16) {
    printf("sizeof(DEVICE_OBJECT) = %d\n", sizeof(DEVICE_OBJECT));
    E(2);
  }

  
  if(sizeof(struct foo) != 16) {
    printf("sizeof(foo) = %d\n", sizeof(struct foo));
    E(3);
  }
  
  if(sizeof(z) != 32)  {
    printf("sizeof(z) = %d\n", sizeof(z));
    E(4);
  }
  
  SUCCESS;
}
