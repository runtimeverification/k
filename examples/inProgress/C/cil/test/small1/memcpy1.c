#include "testharness.h"
#include <string.h>
#include <stdlib.h>

typedef struct {
  char *f1;
  int   f2;
} T1;

// char c1, c2;

// T1 global1;
T1 globarray[5];

// T1 init[] = { 0, 1, &c1, 2, &c2, 3};


//typedef struct {
//  char *w1;
//  int   w2;
//} W1;
//
//W1 wild1, wild2;
//
//int dummy;

void main(void) {
//  T1 x;
  T1 *p = (T1*)malloc(8 * sizeof(T1));

//  memcpy(&x, & init[1], sizeof(T1));
//  if(x.f2 != 2) {
//    exit(1);
//  }
//  if(x.f1 != (char*)&c1) {
//    exit(11);
//  }
//  memcpy(& p[2], init, 2 * sizeof(T1));
//  if(p[2].f2 != 1 || p[3].f2 != 2) {
//    exit(2);
//  }
  memcpy(p, globarray, sizeof(globarray));

//  // Make wild1 wild
//  {
//    W1 *pw;
//    pw = & dummy;
//    pw = &wild1;
//    wild2.w2 = 15;
//    memcpy(pw, &wild2, sizeof(*pw));
//    if(pw->w2 != 15) {
//      exit(3);
//    }
//  }
//
//  {
//    char * as[5];
//    char * ad[5];
//    // Make one of ad a FSEQ
//    ad[4] ++;
//    memcpy(ad, as, sizeof(as));
//  }
  exit(0);
}
