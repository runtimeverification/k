#include "testharness.h"

typedef
void
(*PKNORMAL_ROUTINE) (
     void* NormalContext,
     void* SystemArgument1,
     void* SystemArgument2
    );

typedef struct {
  int info;
  PKNORMAL_ROUTINE fun;
} * PIO_STATUS_BLOCK;

// Make sure we print the __stdcall properly
typedef
void
(__stdcall *PIO_APC_ROUTINE) (
     void* ApcContext,
     PIO_STATUS_BLOCK IoStatusBlock,
     long Reserved
    );



int __stdcall test(int x) {
  return x;
}

PIO_APC_ROUTINE gfun = 0;

int main() {
  return 0;
}
