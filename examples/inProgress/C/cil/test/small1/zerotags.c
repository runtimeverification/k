typedef struct {
	int *foo;
	int bar;
} wildstruct;

int makewild(void *x) {
	return *((int *)x);
} 

int main() {
  wildstruct w;
  int p = 55, q;
  int *ptr;

  makewild(&w);

  w.foo = &p;
  w.foo = 0;

  ptr = w.foo;

  q = *ptr;

  return q;
}
