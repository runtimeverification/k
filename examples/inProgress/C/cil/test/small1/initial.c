#include "testharness.h"

typedef struct {
  int a, b;
} DATA;

typedef struct {
  int tag[5];
  int x;
  DATA d1;
  DATA d2;
} TDATA;


TDATA x = { {0,0,0},
            5 };

TDATA x1 = { .x = 7,
             .d1 = { .b = 5 },
             .d2 = { 9 } };

int main() {
  TDATA x2[] = { [5] = { 8 }} ;
  if(x2[0].x != 0) E(1);

  if(x2[5].x != 0) E(2); // Make sure you zero even after the last init
  if(x2[5].d2.b != 0) E(21);
  if(x2[5].tag[1] != 0) E(22);
  
  if(x2[5].tag[0] != 8) E(3);
  if(sizeof(x2) != 6 * sizeof(TDATA)) E(4);

  SUCCESS;
}


    
