extern struct list {
  struct list *next;
  struct foo *f;
  struct bar *b;
} g;

struct bar {
  enum { A, B, C } e;
};

void* f2() {
  return (void*) & g.b->e;
}


int main() {
  void *v1 = f1(); /* Without prototype */
  void *v2 = f2();
}
