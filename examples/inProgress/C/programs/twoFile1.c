#include <stdio.h>
extern int f(int x, int y);
int z = 5;
static int w = 7;
int q = 3;
int c = 32;
int main(void){
	int q = 4;
	printf("1z = %d\n", z);
	printf("1w = %d\n", w);
	printf("1q = %d\n", q);
	printf("f(2, 3)==%d\n", f(2, 3));
	printf("f(2, 3)==%d\n", f(2, 3));
	printf("f(2, 3) should be 7\n");
	return 0;
}
