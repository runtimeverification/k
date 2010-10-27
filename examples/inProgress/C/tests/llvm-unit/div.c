/* 
 * This file is used to test division operations in conjunction with
 * the Signless Types feature. The DIV instruction was replaced with
 * UDIV, SDIV and FDIV instructions. The tests here are aimed at
 * triggering InstructionCombining transforms to exercise them and
 * ensure they are not altering the computed values.
 */

#include <stdio.h>

unsigned uDivTest1(unsigned X, unsigned Y) {
  /* 0 / X == 0 */
  return 0 / X;
}
unsigned uDivTest2(unsigned X, unsigned Y) {
  /* div X, 1 == X */
  return X / 1;
}
unsigned uDivTest3(unsigned X, unsigned Y) {
  /* div X, -1 == -X */
  return X / -1;
}
unsigned uDivTest4(unsigned X, unsigned Y) {
  /* div X, (Cond ? 0 : Y) -> div X, Y.  */
  return ( X == Y ? 0 : Y );
}
unsigned uDivTest5(unsigned X, unsigned Y) {
  /* div X, (Cond ? 0 : Y) -> div X, Y.  */
  return ( X == Y ? ((unsigned)0) : Y );
}
unsigned uDivTest6(unsigned X, unsigned Y) {
  /* div X, (Cond ? Y : 0) -> div X, Y */
  return ( X != Y ? Y : 0 );
}
unsigned uDivTest7(unsigned X, unsigned Y) {
  /* div X, (Cond ? Y : 0) -> div X, Y */
  return ( X != Y ? Y : ((unsigned)0) );
}
unsigned uDivTest8(unsigned X, unsigned Y) {
  /* (X / C1) / C2  -> X / (C1*C2) */
  return ( X / 2 ) / 4;
}
unsigned uDivTest9(unsigned X, unsigned Y) {
  /* (X / C1) / C2  -> X / (C1*C2) */
  return ( X / ((unsigned)2)) / ((unsigned)4);
}
unsigned uDivTest10(unsigned X, unsigned Y) {
  /* X udiv C^2 -> X >> C */
  return X / 4;
}
unsigned uDivTest11(unsigned X, unsigned Y) {
  /* X udiv C^2 -> X >> C */
  return X / ((unsigned)4);
}
unsigned uDivTest12(unsigned X, unsigned Y) {
  /* X udiv (C1 << N), where C1 is "1<<C2"  -->  X >> (N+C2) */
  return X / (4 << Y);
}
unsigned uDivTest13(unsigned X, unsigned Y) {
  /* X udiv (C1 << N), where C1 is "1<<C2"  -->  X >> (N+C2) */
  return X / (((unsigned)4) << Y);
}
unsigned uDivTest14(unsigned X, unsigned Y) {
  /* udiv X, (Select Cond, C1, C2) --> Select Cond, (shr X, C1), (shr X, C2) */
  return X / (X == Y, 2, 4);
}
unsigned uDivTest15(unsigned X, unsigned Y) {
  /* udiv X, (Select Cond, C1, C2) --> Select Cond, (shr X, C1), (shr X, C2) */
  return X / (X == Y, ((unsigned)2), ((unsigned)4));
}
unsigned uDivTest16(unsigned X, unsigned Y) {
  /* -X/C -> X/-C */
  return -X / 2;
}
unsigned uDivTest17(unsigned X, unsigned Y) {
  /* -X/C -> X/-C */
  return -X / ((unsigned)2);
}

int main(int argc, char**argv) {
  printf("uDivTest1(42,3) = %u\n", uDivTest1(42,3));
  printf("uDivTest2(42,3) = %u\n", uDivTest2(42,3));
  printf("uDivTest3(42,3) = %u\n", uDivTest3(42,3));
  printf("uDivTest4(42,3) = %u\n", uDivTest4(42,3));
  printf("uDivTest5(42,3) = %u\n", uDivTest5(42,3));
  printf("uDivTest6(42,3) = %u\n", uDivTest6(42,3));
  printf("uDivTest7(42,3) = %u\n", uDivTest7(42,3));
  printf("uDivTest8(42,3) = %u\n", uDivTest8(42,3));
  printf("uDivTest9(42,3) = %u\n", uDivTest9(42,3));
  printf("uDivTest10(42,3) = %u\n", uDivTest10(42,3));
  printf("uDivTest11(42,3) = %u\n", uDivTest11(42,3));
  printf("uDivTest12(42,3) = %u\n", uDivTest12(42,3));
  printf("uDivTest13(42,3) = %u\n", uDivTest13(42,3));
  printf("uDivTest14(42,3) = %u\n", uDivTest14(42,3));
  printf("uDivTest15(42,3) = %u\n", uDivTest15(42,3));
  printf("uDivTest16(42,3) = %u\n", uDivTest16(42,3));
  printf("uDivTest17(42,3) = %u\n", uDivTest17(42,3));
  return 0;
}
