#include "testharness.h"

typedef unsigned char __u8;
typedef signed char __s8;


__u8 unsigned uchartest; // This is unsigned char
unsigned char ucharorig;

__u8 signed   signedtest; // This is unsigned char
unsigned char signedorig;


__s8 unsigned uinttest; // This is like unsigned char
unsigned char uintorig;


__s8   long     longtest; // This is just like long
       long     longorig;

__s8  unsigned long     ulongtest; // This is just like unsigned long
      unsigned long     ulongorig;

#define TEST(name, err) \
    name ## test = 255; \
    name ## orig = 255; \
    if(name ## test != name ## orig) E(err + 1); \
                           \
    name ## test = 65000; \
    name ## orig = 65000; \
    if(name ## test != name ## orig) E(err + 2); \
                            \
    name ## test = 130000; \
    name ## orig = 130000; \
    if(name ## test != name ## orig) E(err + 3); \
        /* Test signs */                                         \
    name ## test = -1; name ## test >>= (8 * sizeof(name ## test) - 1); \
    name ## orig = -1; name ## orig >>= (8 * sizeof(name ## orig) - 1); \
    if(name ## test != name ## orig) E(err + 4); \
                                                   
     
int main() {
  TEST(uchar, 0);

  TEST(uint, 20);
  
  TEST(long, 30);

  TEST(ulong, 40);
  
  TEST(signed, 50);

  SUCCESS;
  
}
