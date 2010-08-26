// structattr2.c
// another structure/attribute example
// from sac at stevechamberlain dot com

#include "../small1/testharness.h"

// should associate 'const' with 'b' and 'e', but not 'c'
const struct c  { int a; } b, e;

// so that now, 'd' is *not* const
struct c d;


// Same here
struct c2  { int a; } const b2, e2;

struct c2 d2;


// this const has no effect
struct c3  { int a; } const;
struct c3 b3, e3;

// nor does this one
const struct c4  { int a; };
struct c4 b4, e4;

struct __attribute__((packed)) c5 { char c; int a; } b5, e5;
struct c5 d5;

struct c6 { char c; int a; } __attribute__((packed)) b6, e6;
struct c6 d6;

struct c7 { char c; int a; } __attribute__((packed));
struct c7 b7;

struct c8 { char c; int a; };
struct c8 b8;

TESTDEF baseline: success

TESTDEF archspecific: success

int main() { 
  e.a++;  //KEEP const1: error
  d.a++;
  e2.a++;  //KEEP const2: error
  d2.a++;
  e3.a++;
  e4.a++;
IFTEST archspecific
  //These tests work on a 32-bit machine:
  if (sizeof(e5) != 5) E(5);
  if (sizeof(d5) != 5) E(15);
  if (sizeof(e6) != 5) E(6);
  if (sizeof(d6) != 5) E(16);
  if (sizeof(b7) != 5) E(7);
  if (sizeof(b8) != 8) E(8);
ENDIF
  return 0;
 }

