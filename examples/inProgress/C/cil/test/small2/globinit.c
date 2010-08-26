#include "../small1/testharness.h"
#include "../small1/testkinds.h"

#ifndef __SEQ
#define __SEQ
#define __WILD
#define __INDEX
#endif
// Test the global initializer

// NUMERRORS 14

struct S {
  struct {
    int *p1;
    int  i2;
    int * p3[4];
  } a[4];
  char *f2;
  struct B {
    int *p4;
    int nested [8]; /* Use a large number because CIL does not use long 
                      * initializers if they are 0 */ 
  } b[4];
};

int i1 = 1, i2 = 2, i3 = 3, i4 = 4, i5 = 5;
int ia[8] = { 0, 1, 2, 3, 4, 5, 6, 7};

struct S g = { .a[0].p1 = &i1, .a[0].i2 = 5, .a[0].p3[0] = &i2,
               .a[1].p3[0] = ia, .f2 = "test" };


#if 12 <= ERROR
// Define a long SIZED array of arrays
int matrix[64][4] = { 1, 2, 3 };
#endif

int main() {

  // Test with wildness
#if 1 <= ERROR && ERROR <= 3
  //ERROR(1):Error 1
  {
    struct S * __WILD wg = &g; // Make g WILD
  
    // Test that the address is right
    if(HAS_KIND(&i1, WILD_KIND) && // ERROR(1)
       g.a[0].p1 == &i1 && * g.a[0].p1 == 1) E(1);//ERROR(1)
    if(* g.f2 == 't') E(2);//ERROR(2):Error 2
    // Now check a bit that the tag bits are right
    { int *p = * (int **)(& g.a[0].i2); } //ERROR(3):tampered
  }
#endif

  // Now make sure that we can write SEQ pointers
#if 4 <= ERROR && ERROR <= 6
  {
    int * __SEQ x = g.a[2].p3[1]; // Just to propagate the constraint
    // Make sure that we can read
    if(g.a[1].p3[0] [5] == 5) E(4); // ERROR(4):Error 4
    // Make sure the bounds are right
    { int x = *(g.a[1].p3[0] - 1); } //ERROR(5):Lbound
    { int x = *(g.a[1].p3[0] + 8); } //ERROR(6):Ubound
  }
#endif  

  // Now try the sized arrays
#if 7 <= ERROR && ERROR <= 11
  // Make both the b and the nested array SIZED
  {
    int * __INDEX pnested = g.b[3].nested;
    struct B * __INDEX pb = g.b;
    // Now try to read
    if(! *(pnested + 7)) E(7); //ERROR(7):Error 7
    // Now try to read from outside
    { int x = * (g.b[2].nested - 1); } //ERROR(8):Lbound
    { int x = * (g.b[3].nested + 8); } //ERROR(9):Ubound
    { int x = (g.b - 1)->p4; } //ERROR(10):Lbound
    { int x = (g.b + 4)->p4; } //ERROR(11):Ubound
  }
#endif       

#if 12 <= ERROR && ERROR <= 14
  {
    int * __INDEX x = matrix[4];
    // Now try to read
    if(! *(x + 3)) E(12);//ERROR(12):Error 12
    // Now try to read outside of bounds
    { int y = * (x - 1); } //ERROR(13):Lbound
    { int y = * (x + 4); } //ERROR(14):Ubound
  }
#endif
  
  SUCCESS;
}

