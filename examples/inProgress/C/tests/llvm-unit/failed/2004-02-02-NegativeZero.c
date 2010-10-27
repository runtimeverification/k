void test(double X) {
  printf("%f %f\n", -0.0 - X, -X);
}
int main() {
  test(+0.0);
  test(-0.0);
  printf("negzero = %f  poszero = %f\n", -0.0, +0.0);
  return 0;
}
