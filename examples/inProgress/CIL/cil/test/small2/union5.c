#include "../small1/testharness.h"

#ifndef HAS_KIND
#define HAS_KIND(x, y) 1
#endif

typedef unsigned char MzU8;
typedef unsigned short MzU16;
typedef unsigned int MzU32;
typedef MzU32 MzEventSupp;
struct key_pressed {
   MzU8 repeatCount ;
};
struct char_char {
   MzU8 repeatCount ;
};
struct pointer_moved {
   unsigned int lButton : 1 ;
   unsigned int mButton : 1 ;
   unsigned int rButton : 1 ;
};
union supp {
   MzEventSupp supp ;
   struct key_pressed key_pressed ;
   struct char_char char_char ;
   struct pointer_moved pointer_moved ;
};


int main() {
  union supp *p;
  if(! HAS_KIND(p, SAFE_KIND)) E(1);

  SUCCESS;
}
