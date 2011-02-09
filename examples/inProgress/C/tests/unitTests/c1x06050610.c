#include <stdio.h>
int main(void) {
	int n = 4, m = 3;
	int a[n][m];
	int (*p)[m] = a;
	if (p == &a[0]) {
		printf("p == &a[0]\n");
	} else {
		printf("p != &a[0]\n");
	}
	p += 1;
	if (p == &a[1]) {
		printf("p == &a[1]\n");
	} else {
		printf("p != &a[1]\n");
	}
	(*p)[2] = 99;
	printf("a[1][2] == %d\n", a[1][2]);
	n = p - a;
	printf("n == %d\n", n);
	return 0;
}
