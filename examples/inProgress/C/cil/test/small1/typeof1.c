/* This test case was reported by Robert. It seems that CIL ought to 
 * understand that typeof is an abbreviation */
extern int printf(const char* fmt, ...);

#ifdef __GNUC__
void foo();


__typeof(foo) afun; // A prototype
void afun() {}

void bfun(void); // A prototype for b
extern __typeof(afun) bfun __attribute__ ((alias ("afun"))); // And another

int arr[9];

__typeof(arr) barr = { 0, 1, 2, 3 } ;


__typeof("a long string") str; // Str should have type array, not pointer !

struct foo { int a; int b; };
struct foo returnsAStruct(int a) 
      { return (struct foo){a,2}; }
__typeof(returnsAStruct(42)) a_struct;

#endif


typedef int FUN(int);

FUN fptr; // fptr is defined to be a function! This is a prototype.

FUN fptr; // This is another prototype

int fptr(int x); // Yet another prototype

int fptr(int x) { // Now another definition for it
  return x - 1;
}

typedef int ARRAY[8];

ARRAY carr;

int main(void) 
{
#ifdef __GNUC__ 
  afun();
  bfun();
  /* Let's force CIL to compute some __alignof. This is tricky because it 
   * almost always leaves them alone, except when they are used in 
   * initializer designators */
#define CHECK_CONST(e) {\
    char a[] = { [e] = 34 };\
    printf(# e " = %d (CIL) and %d (Compiler)\n", sizeof(a) - 1, (e)); \
    if(e != sizeof(a) - 1) { exit(1); }\
    }
  CHECK_CONST(sizeof(foo));
  CHECK_CONST(sizeof(afun));
  CHECK_CONST(sizeof("a long string"));
  CHECK_CONST(sizeof(str));
  CHECK_CONST(sizeof(arr));
  CHECK_CONST(sizeof(barr));

  CHECK_CONST(__alignof("a string"));
  CHECK_CONST(__alignof(str));
  CHECK_CONST(__alignof(foo));
  CHECK_CONST(__alignof(afun));
  CHECK_CONST(__alignof(arr));

  // Here CIL is different from GCC: CIL=4, GCC=32?
  // I have no idea where GCC is getting its result from 
  //  CHECK_CONST(__alignof(barr));

#endif
  if(sizeof(carr) != sizeof(ARRAY)) {
    exit(8);
  }
  if (  (sizeof(a_struct) != sizeof(struct foo))
      ||(__alignof(a_struct) != __alignof(struct foo))) {
    exit(9);
  }

  return fptr(1);
}
