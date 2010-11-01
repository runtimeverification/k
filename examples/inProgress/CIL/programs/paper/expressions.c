#include <stdio.h>
int r = 0;
int f (int x) {
	return (r = x);
}
int set(int* loc, int val) {
	return *loc=val;
}
int main(void){

	// int x, example;
	// example = (x=0,x+(x=1));
	// printf("result=%d, x=%d\n", example, x);
	
	// int x, example;
	// example = (x=0) + (x=0);
	// printf("result=%d, x=%d\n", example, x);
	
	// int x, example;
	// example = ((x=2*x)==(x++))&&(++x==x);
	// printf("result=%d, x=%d\n", example, x);
	
	// int example;
	// example = (f(1) + f(2));
	// printf("result=%d, r=%d\n", example, r);
	
	int x, example;
	x = 2;
	example = (set(&x, 2*x)==(x++))&&(set(&x, x + 1)==x);
	printf("result=%d, x=%d\n", example, x);
	// ((Apply(set, ((&(x)) .,.  (2 * x)))==(x ++))&&(Apply(set, ((&(x)) .,.  (x + 1)))== x);)
	
	return 0;
}
