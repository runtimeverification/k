#include "testharness.h"

typedef struct { unsigned long pte_low; } pte_t;


typedef struct { unsigned long pgprot; } pgprot_t;


int main() {
  
  pte_t one, *pte = &one;
  
  *pte = ((pte_t) { ( (( ( 0 ) >> 12  ) << 12 )
                      | ((((pgprot_t) { ( 0x001  | 0x004
                                               | 0x020  ) } )).pgprot)) } );
  if(pte->pte_low != 0x25) E(1);

  SUCCESS;
}

