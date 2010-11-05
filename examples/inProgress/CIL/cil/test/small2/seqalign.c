#include "../small1/testharness.h"

// NUMERRORS 9

char carray[127];
long larray[128];


int main() {
  char * __FSEQ fc  = carray;
  char * __SEQ  sc  = carray;

  long * __FSEQ fl  = larray;
  long * __SEQ  sl  = larray;

  // This should succeed because carray is 127 bytes long.
  fl = (long*) (fc + 3); 

  fl = (long*) (fc + 1); //ERROR(1):unaligned
  sl = (long*) (sc + 4); //ERROR(2):unaligned
  // Now from SAFE -> FSEQ
#if ERROR == 3
  {
    long along;
    long * pl = &along;
    fc = (char*)pl;
    pl = (long*)(fc + 1); //ERROR(3):unaligned
  }
#endif

  // Now from SEQ -> FSEQ
  fl = (long*)(sc + 3); /* should succeed */ E(4);//ERROR(4):Error 4
  fl = (long*)sc; //ERROR(5):unaligned

  // Now through polymorphism
  {
    void * v1 = sc;
    void * v2 = sc + 3;
    if(HAS_KIND(v1, WILD_KIND)) E(16);
    // A good one
    fl = (long*)v2; /* Should be Ok */ E(6);//ERROR(6):Error 6
    fl = (long*)v1;//ERROR(7):unaligned
  }

  // Now test the __align_seq
  fl = (long*)__align_seq(sc, sizeof(*fl)); E(9);//ERROR(9):Error 9
  
  SUCCESS;
}

#if ERROR == 8
// Try a global trick
long * __FSEQ glob = &carray[1]; //ERROR(8):unaligned
#endif
