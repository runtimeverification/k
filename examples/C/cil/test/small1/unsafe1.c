
#include "testharness.h"


typedef struct foo {
  struct foo *next;
  int *data;
} S;

typedef struct not_compatible_with_foo {
    int xxx;
    double *yyy;
} NOT_S;

S array[2];

S *fseq;

int main() {
  NOT_S * data;
  //fseq = array;
  //array[1].next = & array[0];
  //fseq ++;
  
  { __NOCUREBLOCK
      data = (NOT_S *) fseq; // We don't want this cast to polute fseq
  }

  SUCCESS;
   
}
