#include <stdio.h>

int main(void) {
	int i = 2;
	int x;
	x = ((i = 2 * i) == i++) && (++i == i);
	
	printf("x=%d, i=%d\n", x, i);
	return 0;
}
