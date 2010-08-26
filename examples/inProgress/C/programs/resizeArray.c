// Dynamic (re)size array
// adapted from http://www.c.happycodings.com/Data_Structures/code8.html

#include <stdio.h>
#include <stdlib.h>

int main(void) {
	int *a;
	int i = 5;

	if((a = (int *)malloc(i * sizeof(int))) == NULL) {
		printf("Error: failed malloc\n");
		return 1;
	}
	for(i = 0; i < 5; i++) 
		a[i] = i;

	printf("-- array after malloc\n");
	for(i = 0; i < 5; i++) 
		printf(" a[%d] = %d\n", i, a[i]);

	if((a = (int *)realloc(a, 10 * sizeof(int))) == NULL) {
		printf("Error: failed realloc\n");
		return 1;
	}
	for(i = 0; i < 10; i++) 
		a[i] = i;

	printf("\n-- array after realloc\n");
	for(i = 0; i < 10; i++) 
		printf(" a[%d] = %d\n", i, a[i]);

	free(a);
	return 0;
}
