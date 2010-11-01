
int *globptr;

int global;

int foo() {
  int local;
  int *s = &local; s += (&global - s); // s == &global but with the home of the local
  globptr = s; // Store away the pointer. Succeeds because s's value is not on the stack
  return (int)&local; // We'll need this later
}

int main() {
 int localaddr = foo();
 globptr += (localaddr - (int)globptr);// glob == &local with the home of the &local 
 return *globptr; // We are reading from a dead stack frame
}
