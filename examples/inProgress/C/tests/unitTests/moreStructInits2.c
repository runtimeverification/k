// based on 20071202-1.c from gcc c torture test suite
#include <stdio.h>
struct T { int t; int r[8]; };
struct S { int a; int b; int c[6]; struct T d; };

int main (void) {
	struct S s = { 6, 12, { 1, 2, 3, 4, 5, 6 }, { 7, { 8, 9, 10, 11, 12, 13, 14, 15 } } };
		 
	printf("%d\n", s.a);
	printf("%d\n", s.b);
	for (int i = 0; i < 6; i++){
		printf("%d\n", s.c[i]);
	}
	printf("%d\n", s.d.t);
	for (int i = 0; i < 8; i++){
		printf("%d\n", s.d.r[i]);
	}
	return 0;
}
