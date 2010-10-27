#include <stdio.h>

void testCastOps(int y) {
  printf("y = %d, (y == 2 || y == 0) == %d\n",
         y, ((_Bool) (y == 2)) || ((_Bool) (y == 0)));
  printf("y = %d, (y > 2 || y < 5) == %d\n",
         y, ((_Bool) (y < 2)) && ((_Bool) (y > -10)));
  printf("y = %d, (y ^ 2 ^ ~y) == %d\n",
         y, (_Bool) (y ^ 2 ^ ~5));
}

void testBool(_Bool X) {
  printf("%d\n", X);
}

void testByte(char X) {
  printf("%d ", X);
  testBool(X != 0);
}

void testShort(short X) {
  printf("%d ", X);
  testBool(X != 0);
}

void testInt(int X) {
  printf("%d ", X);
  testBool(X != 0);
}

void testLong(long long X) {
  printf("%lld ", X);
  testBool(X != 0);
}

int main() {
  testByte(0);
  testByte(123);
  testShort(0);
  testShort(1234);
  testInt(0);
  testInt(1234);
  testLong(0);
  testLong(123121231231231LL);
  testLong(0x1112300000000000LL);
  testLong(0x11120LL);
  testCastOps(2);
  return 0;
}
