struct tm {
  int x;
};

/* Various ways to place attributes */
char *  __cdecl asctime1(const struct tm *);
char * __stdcall asctime2(const struct tm *);
unsigned long __cdecl _exception_code(void);

__declspec(dllimport)
unsigned long 
__stdcall
Int64ShllMod32 (void (__stdcall *)());

__inline unsigned long
__stdcall
Int64ShlrMod32 ( int Value);

typedef struct {
  int (__stdcall *foo)();
} T1;

typedef int (__cdecl *BAR)();

int * (__stdcall * x1[8])(void); // Array of function pointers

void __stdcall foo(int x) {
  return;
}

void main() {
  struct tm thetime;
  BAR bar;
  char *t1 = asctime1(& thetime);
  char *t2 = asctime2(& thetime);
  unsigned long l = Int64ShllMod32( & foo );
}


