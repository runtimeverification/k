#include <stdio.h>

struct vec2 { double X, Y; };

void print(struct vec2 S) {
	printf("%d, %d\n", (int)(10000 * S.X), (int)(10000 * S.Y));
}

int main() {
	struct vec2 U;
	U.X = .5; U.Y = 1.2;
	print(U);
	return 0;
}
