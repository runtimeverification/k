/* This exhibits a bug with the types of tagged functions whose arguments 
 * appear tagged */
int foo(int x);

struct S {
  void (*fptr)();
} g = { &foo };

int main() {
  // Make g (and thus foo) TAGGED
  int *pg = (int*)&g;
}

int foo(int arg) {
  // Now take the address of x and make it tagged
  int **px = &arg;
  return arg;
}
