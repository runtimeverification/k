#include <stdio.h>
int z;
static int w = 13;
static int r = 15;

static int g(int x) {
	return x * x;
}

typedef double myvar;
int f (int x, int y) {
	static int r;
	r++;
	extern int c;
	myvar v = 2.3;
	printf("  2z = %d\n", z);
	printf("  2w = %d\n", w);
	printf("  2r = %d\n", r);
	printf("  2c = %d\n", c);
	printf("  2g(5) = %d\n", g(5));
	printf("  2v = %d\n", (int)(v*1000));
	return x * 2 + y;
}
