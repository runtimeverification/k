#include <stdio.h>
#include <string.h>
int main() {
  double a[2][2];
  memcpy(a, (double[2][2]) { { 1.0, 2.0 } , { 3.0, 4.0 } }, sizeof a);
  printf("%f %f %f %f\n", a[0][0], a[0][1], a[1][0], a[1][1]);
  return 0;
}
