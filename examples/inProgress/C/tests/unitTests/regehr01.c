#include <stdio.h>
static int x ;
static int *volatile z = &x;
static int foo (int* y) {
	return *y;
}
int main(void){
	*z = 1;
	printf("%d\n", foo(&x));
	return 0;
}

