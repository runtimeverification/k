// structattr3.c
// yet more experiments


struct S { char a; } __attribute__((aligned(8))) const  x = {1};

struct S y[10] = {1,2,3};
int z = 5;

int main() { return 0; }
