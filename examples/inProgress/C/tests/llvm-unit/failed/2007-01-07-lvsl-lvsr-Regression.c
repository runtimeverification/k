#include <stdio.h>
#include <altivec.h>

__vector unsigned char C_uchar1[2] = {
  { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
  { 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35 }
};
__vector unsigned char C_uchar2[2] = {
  { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
  { 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35 }
};

void print_vector(__vector unsigned char v) {
  unsigned *vp = (unsigned *)&v;
  printf("%08x%08x%08x%08x\n", vp[0], vp[1], vp[2], vp[3]);
}

int main(int argc, const char * argv[]) {
  C_uchar1[0] = (__vector unsigned char)__builtin_altivec_lvsl(1,
                                                             (void *)&C_uchar1); 
  C_uchar2[0] = (__vector unsigned char)__builtin_altivec_lvsr(1,
                                                             (void *)&C_uchar2); 
  print_vector(C_uchar1[0]);
  print_vector(C_uchar1[1]);
  print_vector(C_uchar2[0]);
  print_vector(C_uchar2[1]);
  return 0;
}
