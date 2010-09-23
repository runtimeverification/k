int z;
static int w = 13;
static int r = 15;
int f (int x, int y) {
	static int r;
	r++;
	extern int c;
	printf("  2z = %d\n", z);
	printf("  2w = %d\n", w);
	printf("  2r = %d\n", r);
	printf("  2c = %d\n", c);
	return x * 2 + y;
}
