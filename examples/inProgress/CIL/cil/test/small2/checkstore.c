#include "../small1/testharness.h"
#include "../small1/testkinds.h"

// NUMERRORS 13


struct aPointer {
  int* p;
};

//Store one local inside another.
void storeLocals(void)
{
  int a;
  struct aPointer localStruct;
  int b;
  struct aPointer *plocalStruct;
  plocalStruct = &localStruct; //Try to confuse CCured about whether *plocalStruct is local.

  localStruct.p = &a;

  //These should be legal, even though b is lower on the stack than localStruct.
  plocalStruct->p = &a;
  plocalStruct->p = &b;
}

//Store a stack variable that sits higher in the stack inside a local
void storeToStack(int* pStack)
{
  struct aPointer localStruct;
  struct aPointer *plocalStruct = &localStruct;

  //This should be legal, since localStruct will go away before *pStack does.
  plocalStruct->p = pStack;
}

int *gptr;

int global;

int function() {
  int local;

  // This should work
  gptr = &global; //ERROR(0)

  // so should this
  storeLocals();
  // and this
  storeToStack(&local);

  // This should fail
  gptr = &local; // ERROR(1):STORE_SP

  // Play a trick with pointer arithemtic (SEQ)
#if ERROR == 2
  {
    // ERROR(2):Storing stack address
    int *t = &local; t += (&global - t);
    if(! HAS_KIND(t, SEQ_KIND)) E(2);
    gptr = t; // Should fail
    local = *(gptr + (&local - gptr));
  }
#endif

  // The same trick with WILD
#if ERROR == 3
  {
    // ERROR(3):Storing stack address
    int *t = (int**)&local; // t is WILD now
    if(! HAS_KIND(t, WILD_KIND)) E(3);
    t += (&global - t); gptr = t; // Should fail
  }
#endif
  
  // The same trick with FSEQ
#if ERROR == 4
  {
    //matth:  we get an LBound failure in Linux in "f = s" because the global is 
    // stored below the stack.  In windows, we get a UBound failure converting f 
    // to a SAFE in "gptr = f" because the global is above the stack.
    // ERROR(4):bound
    int *f = &local;
    int *s = &local; s += (&global - s); // s is SEQ
    f ++; // f has type FSEQ
    if(! HAS_KIND(f, FSEQ_KIND)) E(4);
    f = s; //Actually we fail here because s is below its home
    gptr = f; // Should fail
  }
#endif
  

  // Now writing structures
#if 5 <= ERROR && ERROR <= 7
  {
    static struct str1 {
      int i1;
      struct {
        int *s2;
      } i2;
      int * i3;
    } gstr;
    struct str1 res = { 0, &global, &global };//ERROR(5):Error 5
    struct str1 res = { 0, &local, &global };//ERROR(6):Storing stack address
    struct str1 res = { 0, &global, &local };//ERROR(7):Storing stack address
    gstr = res;
    E(5);
  }
#endif

  // Now write an array
#if 8 <= ERROR && ERROR <= 10
  {
    static struct strarr {
      int *a[4];
    } garr;
    struct strarr res = { &global, &global, &global };//ERROR(8):Error 8
    struct strarr res = { 0, &local, &global };//ERROR(9):Storing stack address
    struct strarr res = { 0, &global, &local };//ERROR(10):Storing stack address
    garr = res;
    E(8);
  }
#endif

  // Now write a union
#if 11 <= ERROR && ERROR <= 13
  {
    static union un {
      int *a[4];
      struct { int *a1, *a2, *a3; } b;
    } gun;
    union un res = { &global, &global, &global };//ERROR(11):Error 11
    union un res = { 0, &local, &global };//ERROR(12):Storing stack address
    union un res = { 0, &global, &local };//ERROR(13):Storing stack address
    gun = res;
    E(11);
  }
#endif

  //make this function look recursive to discourage inlining.
  // (if we are inlined into main, then 'local' looks like one of main's
  // locals, and will be treated like a global because we treate main 
  // as a special case.)  
  if (gptr == 0xdeadbeef) {
    function ();
  }
  
}


// We must do all tests not in main, because CCured now allows
// addresses of locals in main to be stored into the heap
int main() {
  function();
}
