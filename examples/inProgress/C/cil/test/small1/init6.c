#include "testharness.h"

struct A {
  struct S { int x; } s;
  int a[4];
  int  : 8;  // Unnnamed field
  int *p;
};

struct S s = { 8 };

struct B {
  struct A a1;
  struct A a2;
  struct A a3;
  struct A a4;
  struct A a5;
};

struct A a = { 1, 2, 3, 4, 5, 6 };


int main() {
  struct B b = { .a2 = { .s = { .x = 5 }}, // a2
                 s, 0, 0, 0, 0, 0,  // a3
                 6, { 0 }, 0,  // a4
                 a // a5
  } ;
  
  if(s.x != 8) E(2);

  if(a.s.x != 1 || a.a[1] != 3 || a.p != 6) E(3);

  if(b.a2.s.x != 5) E(1);

  if(b.a2.a[2] != 0) E(4);

  if(b.a3.s.x != s.x) E(5);

  if(b.a4.s.x != 6) E(6);

  if(b.a5.a[2] != a.a[2]) E(7);

  {
    struct B b1 = { .a2 = a,
                    .a1 = b.a4 };

    if(b1.a2.a[2] != a.a[2]) E(11);
                    
    if(b1.a1.s.x != b.a4.s.x) E(12);
                    
  }

  {
    struct B b2 = { .a2.a[1 ... 2] = 7, 8, 9, // a2.a[1], [2] and [3], a2.p
                    10, 11, 12, 13, 14,  // a3 
                    .a1.s.x = 15, 16, 17, 18, 19, 20,// a1.s.x a1.a[0 ...3], p
                    21, 22, 23, // a2.s.x a2.a[0..1]
                    .a3.p = 8, // Overwrite the 14 from above
    };

    if(b2.a2.a[0] != 22) E(20);
    if(b2.a2.a[1] != 23) E(21);
    if(b2.a2.a[2] != 7) E(22);
    if(b2.a3.s.x  != 10) E(23);
    if(b2.a3.a[0] != 11) E(24);
    if(b2.a3.a[1] != 12) E(25);
    if(b2.a3.a[2] != 13) E(26);
    if(b2.a3.a[3] != 14) E(27);
    if(b2.a3.p    != 8) E(28); // Was overwritten later

    if(b2.a1.s.x != 15) E(29);
    
    if(b2.a1.a[0] != 16) E(30);
    if(b2.a1.a[1] != 17) E(31);
    if(b2.a1.a[2] != 18) E(32);
    if(b2.a1.a[3] != 19) E(33);

    if(b2.a1.p != 20) E(34);
    
    if(b2.a2.s.x  != 21) E(35);
  }
  
  SUCCESS;
  
}

