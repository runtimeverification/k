#include "testharness.h"

typedef unsigned long ULONG;
typedef long LONG;
#ifdef _GNUCC
typedef long long LONGLONG;
#else
typedef __int64 LONGLONG;
#endif

typedef union _LARGE_INTEGER {
  struct {  
    ULONG LowPart;
    LONG HighPart;
  };  
  struct {
    ULONG LowPart;
    LONG HighPart;
  } u;
    LONGLONG QuadPart;
} LARGE_INTEGER;


int main() {
  LARGE_INTEGER foo;

  foo.LowPart = 3;
  foo.HighPart = 7;

  if (foo.u.LowPart != 3) {
    E(1);
  } 
  if (foo.u.HighPart != 7) {
    E(2);
  } 

  
  SUCCESS; 
}

