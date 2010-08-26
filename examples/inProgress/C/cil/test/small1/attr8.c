void foo(char * x) __attribute__((__volatile__));
void foo(char * x) {
  while(1) { ; } 
}

int main(int argc, char **argv) {
  foo(0);
  return 0;
}

