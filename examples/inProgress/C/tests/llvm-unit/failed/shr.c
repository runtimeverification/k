/*
 * This file is used to test shift right operations in conjunction with
 * the Signless Types features. The SHR instruction was replaced with
 * LSHR, ASHR instructions. The tests here are aimed at triggering 
 * InstructionCombining transforms to exercise them and ensure they are
 * not altering the computed values.
 */

#include <stdio.h>

unsigned ShrTest1(unsigned X, unsigned C1, unsigned C2) {
  // (ushr X, C1) & C2 == 0  iff (-1 >> C1) & C2 == 0
  return (X >> C1) & C2;
}

int ShrTest2(int X, unsigned C1, int C2) {
  // (ashr X, C1) & C2  -> (lshr X, C1) & C2  if C2 only has low-bit set
  return (X >> C1) & C2;
}

int ShrTest3(int X) {
  // -((uint)X >> 31) -> ((int)X >> 31)
  return -((unsigned)X >> 31);
}

unsigned ShrTest4(int X) {
  // -((int)X >> 31) -> ((uint)X >> 31)
  return -(X >> 31);
}

unsigned ShrTest5(unsigned X, unsigned C) {
  // (X >> C) & AndRHS) -> X >> C if AndRHS == AllOne >> C
  unsigned AndRHS = (unsigned)0xFFFFFFFF >> C;
  return (X >> C) & AndRHS;
}

unsigned ShrTest6(int X, unsigned C) {
  // (X >>s C) & AndRHS) -> X >> C if AndRHS == AllOne >> C
  int AndRHS = (unsigned)0xFFFFFFFF >> C;
  return (X >> C) & AndRHS;
}

int ShrTest7(int X) {
  // shr X, 0 == X
  return X >> 0;
}

int ShrTest8(unsigned C) {
  // ashr -1, C == -1
  return -1 >> C;
}

int ShrTest9(int Y, int X, unsigned C) {
  // (Y + (X >> C)) << C  ->  (X + (Y << C) & (~0 << C)
  return (Y + (X >> C)) << C;
}

int ShrTest10(int Y, int X, unsigned C) {
  // (Y & (X >> C)) << C  ->  (X & (Y << C) & (~0 << C)
  return (Y & (X >> C)) << C;
}

int ShrTest11(int Y, int X, unsigned C) {
  // (Y | (X >> C)) << C  ->  (X | (Y << C) & (~0 << C)
  return (Y | (X >> C)) << C;
}

int ShrTest12(int Y, int X, unsigned C, int CC) {
  // (Y + ((X >> C) & CC)) << C  ->  ((X & (CC << C)) + (Y << C))
  return (Y + ((X >> C) & CC)) << C;
}

int ShrTest13(int Y, int X, unsigned C, int CC) {
  // (Y & ((X >> C) & CC)) << C  ->  ((X & (CC << C)) & (Y << C))
  return (Y & ((X >> C) & CC)) << C;
}

int ShrTest14(int Y, int X, unsigned C, int CC) {
  // (Y | ((X >> C) & CC)) << C  ->  ((X & (CC << C)) | (Y << C))
  return (Y | ((X >> C) & CC)) << C;
}

unsigned ShrTest15(unsigned A, unsigned C1, unsigned C2) {
  // (A << C1) >> C2  ->  (A & (0xFFFFFFFF >>u C2)) << |C1-C2|
  return (A << C1) >> C2;
}

int ShrTest16(int X, unsigned C1, unsigned C2) {
  // (X >>s C1) << C2 where C1 > C2  ->  (X >>s (C1-C2)) & mask
  // mask = X & (0xFFFFFFFF << C2)
  return (X >> C1) << C2;
}

int main(int argc, char **argv) {
  printf("ShrTest1(-1, 11, 0xFF000000) = %d\n", 
          ShrTest1(0xFFFFFFFF, 11, 0xFF000000));
  printf("ShrTest2(-73, 11, 1) = %d\n", ShrTest2(-73, 11, 1));
  printf("ShrTest3(-73) = %d\n", ShrTest3(-73));
  printf("ShrTest4(-73) = %d\n", ShrTest4(-73));
  printf("ShrTest5(7773, 11) = %d\n", ShrTest5(7773, 11));
  printf("ShrTest6(-73, 11) = %d\n", ShrTest6(-73, 11));
  printf("ShrTest7(-737) = %d\n", ShrTest7(-737));
  printf("ShrTest8(73) = %d\n", ShrTest8(73));
  printf("ShrTest9(13, 7773, 11) = %d\n", ShrTest9(13, 7773, 11));
  printf("ShrTest10(13, 7773, 11) = %d\n", ShrTest10(13, 7773, 11));
  printf("ShrTest11(13, 7773, 11) = %d\n", ShrTest11(13, 7773, 11));
  printf("ShrTest12(7773, -73, 11, 3773) = %d\n", ShrTest12(7773, -73, 11, 3773));
  printf("ShrTest13(7773, -73, 11, 3773) = %d\n", ShrTest13(7773, -73, 11, 3773));
  printf("ShrTest14(7773, -73, 11, 3773) = %d\n", ShrTest14(7773, -73, 11, 3773));
  printf("ShrTest15(7773, 13, 11) = %d\n", ShrTest15(7773, 13, 11));
  printf("ShrTest16(-73, 11, 13) = %d\n", ShrTest16(-73, 11, 13));
  return 0;
}
