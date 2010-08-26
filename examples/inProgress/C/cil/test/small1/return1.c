
void destroy(int *x) {
  x = 0;
}

int main() {
  int x;
  return destroy(&x), 0 ;
}
