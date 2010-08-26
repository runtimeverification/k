/* A test in which two structs in the same file end up being
   constrained to be isomorphic. We have to pick the earliest-defined as a 
   * representative. We have two sets of tests trying to catch the error no 
   * matter in which order we do the unification. */
extern struct s1 {
  int x;
} x1;
extern struct d1 {
  double x;
} y1;

/* Use s1 and d1 in some way */
struct use {
  struct s1 f1;
  struct d1 f2;
} ext1;

extern struct s11 {
  int x;
} x2;
extern struct d11 {
  double x;
} y2;

/* Use s11 also  */
struct use2 {
  struct s11 f2;
  struct d11 f3;
} ext2;


#include "testharness.h"
int main() {
  printf("Address of x1=%x and x2=%x\n",
         &x1, &x2);
  printf("Address of y1=%x and y2=%x\n",
         &y1, &y2);
}
