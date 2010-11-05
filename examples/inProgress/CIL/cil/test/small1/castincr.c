#include <stdio.h>
#include <stdlib.h>

int main(void) {
	char *p;
	int i;

	p = malloc(2*sizeof(int));
	*(int *)p       = 1;
	*((int *)p + 1) = 2;

	i = *((int *)p)++;
	printf("%d\n", i);
	i = *((int *)p)++;
	printf("%d\n", i);

	return 0;
}
