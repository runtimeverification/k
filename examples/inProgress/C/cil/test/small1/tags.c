

// A few test cases for tags

typedef struct {
  int  x;
  char *p;
  int a[20];
} S1;

typedef struct {
  S1 s1test;
  double f1, f2;
} S2;


int extint = 5;
S1  exts1 = { 7, 0 };
S2  exts2;

int *fooptr = 5;

extern extarr[];
extern struct {
  int i1, i2;
  int a[4];      // sm: this was a[], but that's an error right??
} extstruct;


int foo(int k) {
  int t = extint + extarr[5];
  S2  locs2;

  * ((int*)& locs2) = 0;  // The & counts here

  
}
