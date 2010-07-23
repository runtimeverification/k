#include "../small1/testharness.h"

// NUMERRORS 3

union {  //size = 12
  struct {
    int *a, *b;
  } f1;
  int f2;

  // An ugly, unrealistic case
  struct {  //size = 12
    union {  //size = 8
      int x;
      struct {  //size = 8
        int* s1;
        int* s2;
      } s;
    } __TAGGED f3_u;
    int f3_int;
  } f3;

} __TAGGED u;

int i;

int main() {
  
  u.f2 = 5; // now u.f1.a = 5
  u.f1.b = &i; // now the tag says that u.f1 is active

  i = * u.f1.a; //ERROR(1): Null pointer

  u.f2 = 5; // now u.f3.f3_u.s.s1 = 5

  //Union in a union.  This will clear the f3 struct and (redundantly) the 
  // f3.f3_u.s struct.

  u.f3.f3_u.s.s2 = &i;
#if ERROR == 0
  if (u.f3.f3_u.s.s2 != &i) E(1);
  if (u.f3.f3_u.s.s1 != 0) E(2);
  if (u.f3.f3_int != 0) E(3);
  if (! CCURED_HASUNIONTAG(u.f3.f3_u.s.s1)) E(4);
  if (CCURED_HASUNIONTAG(u.f3.f3_u.x)) E(5);
  if (CCURED_HASUNIONTAG(u.f1.a)) E(6);

#else
  i = * u.f3.f3_u.s.s1; //ERROR(2): Null pointer
  i = * u.f1.b; //ERROR(3): WRONGFIELD
#endif

  SUCCESS;
}
