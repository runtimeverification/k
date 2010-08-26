int g1, g2, g3, g4, g5;


int test2(int a) {
  g1 = g2+g3;
  return g1;
}

int test3(int a) {
  int b;
  b = g3+test2(5);
  g2=b;
  return b;
}

int test4(int a) {
  int a;
  a = test3(5);
  test3(6);
  return a;
}
  
  
int main() { return 0; }
