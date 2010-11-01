#include <stdio.h>
int main(void){
	unsigned char x;
	unsigned char y;
	y = x;
	if (x != y){
		printf("BUG: can't compare unknowns\n");
	}
	return 0;
}
