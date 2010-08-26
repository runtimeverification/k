//Make sure everything runs as is
//KEEP baseline: success

#include "../small1/testharness.h"


typedef struct parent {
  void * __RTTI * vtbl;
  int  *fseq;
  int  *f1;
} Parent;

#pragma ccured_extends("Schild", "Sparent")

typedef struct child {
  void * __RTTI * vtbl;
  int  * __FSEQ fseq;
  int  *f1;
  int  f2;
} Child;


//OpenSSL does casts between union fields like this.
union {
  int i;
  void* vp;
  int* ip;
  char* str;
  double d;
  Parent * __RTTI pp;
  Child *  cp;
  int** ptrptr;
} __TAGGED u;

int global[11];

int* foo(int* x) { return x; }

int main() {
  Child carray[5];
  Parent parray[2];

  u.ip = foo(&global[0]);
  unsigned long x = u.vp;
  x += u.i;
  u.ip++;  //KEEP fseq: success
  x += *u.ip;

  u.i = x; //KEEP wrongfield: error = wrong union field
  void* __RTTI v = u.vp;

  u.str = "literal";  //KEEP str: success
  v = u.vp;           //KEEP str
  printf((char*)v);   //KEEP str

  u.cp = &carray[2];
  Parent * __RTTI p= u.pp;
  if (__endof(p) != (unsigned long)(carray + 5)) E(2);  //KEEP fseq
  Child * c = p;
  c++;           //KEEP fseq
  x += c->f2;

  u.vp = p; //make sure we preserve the RTTI.
  x += u.cp->f2;

  u.d = 1.0 / 10;  //DROP double: error = wrong union field
  double dd = u.d;

  //Use a union to cast an int* __FSEQ * to void* __RTTI, and back to int**.
  //Make sure the right compatibility edges are added.
  int * z2 = &global[0];
  int* __FSEQ z = global;                       //KEEP ptrptr: success
  u.ptrptr = &z;                                //KEEP ptrptr
  void * __RTTI r = u.vp;                       //KEEP ptrptr
  *((int**)r) = z2;   // z2 should be FSEQ!     //KEEP ptrptr
  if (KIND_OF(z) != FSEQ_KIND) E(3);            //KEEP ptrptr
  if (KIND_OF(z2) != FSEQ_KIND) E(4);           //KEEP ptrptr

  if (KIND_OF(z2) != SAFE_KIND) E(5);           //DROP ptrptr
  
  //The dual of the above test: RTTI first, then the union.
  int * z3 = &global[0];
  void * __RTTI r = &z3;                        //KEEP ptrptr2: success
  u.vp = r;                                     //KEEP ptrptr2
  int* __FSEQ z = global;                       //KEEP ptrptr2
  (*(u.ptrptr))++;                              //KEEP ptrptr2
  // u.ptrptr (and therefore z3) should be FSEQ!
  if (KIND_OF(z) != FSEQ_KIND) E(6);            //KEEP ptrptr2
  if (KIND_OF(z3) != FSEQ_KIND) E(7);           //KEEP ptrptr2

  if (KIND_OF(z3) != SAFE_KIND) E(8);           //DROP ptrptr2

  int* __FSEQ z = global;
  void* __RTTI r = &z;


  SUCCESS;
}
