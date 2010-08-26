int g;

void F() {
  int a;
  if (a>5) { g = 3; }
}

int main() {
  g = 4;
  F();
}
