
#pragma warning(foo:2)

// Various attributes
int array[32];

int foo, bar, c;

int * __attribute__((array)) p1;
#ifdef CIL
 int * __attribute__((test(foo ? bar : c))) p4;

 // The following is about a grammar conflict with 5:6 in pragmas
 // Too bad we have to parenthesize the (0) like that
 int * __attribute__((test(foo ? (0) : 1))) p5;

 int * __attribute__((test(foo ? bar : 1))) p6;


 int * __attribute__((test(&array))) p2;
 int * __attribute__((test(&array[0]))) p3;
#endif

int main() {
  return 0;
}
