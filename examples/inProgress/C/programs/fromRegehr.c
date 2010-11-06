#include <stdio.h>
int g = 1;

int func() {
	g = 2;
	return 3;
}

int main() {
	int *l = &g;
	*l = func();
	printf("%d\n", g);
	return 0;
}
