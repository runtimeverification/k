int main(void) {
	int x = 0;
	int y = 0;
	int n;
	do {
		int result = 0;

		for (n = 0; n < x; n++, y++)
			result += 5;
		x += 1;
	} while (x < 5);
	return 0;
}
