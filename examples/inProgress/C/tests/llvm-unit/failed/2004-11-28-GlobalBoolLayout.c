#include <stdlib.h>
#include <stdio.h>

struct S { _Bool X, Y; char str[100]; };

struct S G = { 1, 1, "fooo" };

int main() {
	int X = strlen(G.str);
	if (X == 10) {
	  scanf("%d, %d\n", &G.X, &G.Y);
        }
	printf("%d %d %d\n", G.X, G.Y, X);
	return X-4;
}

