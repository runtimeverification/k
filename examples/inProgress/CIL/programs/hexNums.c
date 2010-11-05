#include <stdio.h>
#include <limits.h>

void foo (int a) {
	int b = (a - 1) + INT_MIN;
	if (b != INT_MIN)
		printf("b not INT_MIN\n");
}

int main (void) {
	foo(1);
	return 0;
}
