#include <stdio.h>

struct vec2 { double X, Y; };

void print(struct vec2 S, struct vec2 T) {
	printf("%d, %d, %d, %d\n", (int)(10000 * S.X), (int)(10000 * S.Y), (int)(10000 * T.X), (int)(10000 * T.Y));
}

int main() {
	struct vec2 U, V;
	U.X = .5; U.Y = 1.2;
	V.X = -123.01; V.Y = 1/3.0;
	print(U, V);
	return 0;
}
