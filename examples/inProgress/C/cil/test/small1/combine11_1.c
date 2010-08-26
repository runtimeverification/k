/* We have two files, each with part of a structure undefined */
struct list {
  struct list *next;
  struct foo *f;
  struct bar *b;
} g;

struct foo {
  double d;
};

extern void* f2();
void* f1() {
  return (void*) & g.f->d;
}
