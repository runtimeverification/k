typedef int __intptr_t;
typedef int intptr_t;

extern  intptr_t foo(void);

int main() {
  intptr_t x = foo();
  return x;
}
