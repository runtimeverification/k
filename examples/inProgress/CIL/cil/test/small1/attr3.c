/* Test the parsing of types */
#define NORET __attribute__((noreturn))
#define SECTION __attribute__((section("foo")))
#define A(n)    __attribute__((a(n)))
#define A1 A(1)
#define A2 A(2)
#define A3 A(3)
#define A4 A(4)
#define A5 A(5)
#define A6 A(6)
#define A7 A(7)
#define A8 A(8)
#define A9 A(9)
#define N __attribute__((name))



/* Array (A1) of pointers (A2) to functions (A3) that take an int (A4) and 
 * return a pointer (A5) to int (A6)  */
int A6 * A5 (A3 * A2 (A1 x1)[5])(int A4) N;


/* A function (A4) that takes a float (A5) and returns a pointer (A6) to an 
 * int (A7) */
extern int A7 * A6 (A4 x2)(float A5 x) N;

/* A function (A1) that takes a int (A2) and that returns a pointer (A3) to 
 * a function (A4) that takes a float (A5) and returns a pointer (A6) to an 
 * int (A7) */
int A7 * A6 (A4 * A3 (A1 x3)(int A2 x))(float A5) {
  return & x2;
}
