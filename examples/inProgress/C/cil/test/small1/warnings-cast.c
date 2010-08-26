const int a = 3;

const int *f() {
  return &a;
}

int main() {
  // Make sure we keep the cast from "const int*" to "int*"
  // If it's dropped, gcc emits a warning.
  int *p = (int*) f();
  *p = 4;
  return *p;
} 
