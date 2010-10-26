// this test is based off of 2071202-1.c in the gcc c torture test suite
#include <stdio.h>

struct T { int t; int r[8]; };
struct S { int a; int b; int c[6]; struct T d; };

void foo (struct S *s) {
	printf("%d\n", s->a);
	printf("%d\n", s->b);
	printf("%d\n", s->c[0]);
	printf("%d\n", s->c[1]);
	printf("%d\n", s->c[2]);
	printf("%d\n", s->c[3]);
	printf("%d\n", s->c[4]);
	printf("%d\n", s->c[5]);
	printf("%d\n", s->d.t);
	printf("%d\n", s->d.r[0]);
	printf("%d\n", s->d.r[1]);
	printf("%d\n", s->d.r[2]);
	printf("%d\n", s->d.r[3]);
	printf("%d\n", s->d.r[4]);
	printf("%d\n", s->d.r[5]);
	printf("%d\n", s->d.r[6]);
	printf("%d\n", s->d.r[7]);
	*s = (struct S) { s->b, s->a, { 0, 0, 0, 0, 0, 0 }, s->d };
}

int main (void) {
	struct S s = { 6, 12, { 1, 2, 3, 4, 5, 6 }, { 7, { 8, 9, 10, 11, 12, 13, 14, 15 } } };
	foo (&s);
	
	printf("%d\n", s.a);
	printf("%d\n", s.b);
	printf("%d\n", s.c[0]);
	printf("%d\n", s.c[1]);
	printf("%d\n", s.c[2]);
	printf("%d\n", s.c[3]);
	printf("%d\n", s.c[4]);
	printf("%d\n", s.c[5]);
	printf("%d\n", s.d.t);
	printf("%d\n", s.d.r[0]);
	printf("%d\n", s.d.r[1]);
	printf("%d\n", s.d.r[2]);
	printf("%d\n", s.d.r[3]);
	printf("%d\n", s.d.r[4]);
	printf("%d\n", s.d.r[5]);
	printf("%d\n", s.d.r[6]);
	printf("%d\n", s.d.r[7]);
	
	return 0;
}
