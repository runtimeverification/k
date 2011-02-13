// based on test 20000227-1.c from gcc torture tests
static const unsigned char f[] = "\377";
static const unsigned char g[] = "ÿ";

int main(void) {
	if (sizeof f != 2)
		return 1;
	if (sizeof g != 2)
		return 2;
	if (f[0] != g[0])
		return 3;
	if (f[1] != g[1])
		return 4;
	// if (f[2] != g[2])
		// return 5;
	return 0;
}
