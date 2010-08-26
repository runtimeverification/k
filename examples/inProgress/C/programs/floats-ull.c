#include <stdio.h>

unsigned long long int f2ull(float f) {
	return (unsigned long long int) f;
}
unsigned long long int d2ull(double d) {
	return (unsigned long long int) d;
}

int main(void){
	if (f2ull(1.99) != 1LL) {
		puts("Messed up 1.99");
	}
	unsigned long long int innerInt = (~0ULL) >> 1;
	float innerFloat = (float) (innerInt);
	unsigned long long int lhs_ull = f2ull(innerFloat);
	unsigned long long int choice1 = (~0ULL) >> 1;
	unsigned long long int choice2 = ((~0ULL) >> 1) + 1;

	if (lhs_ull != choice1 &&	/* 0x7fffffff */
		lhs_ull != choice2) {
		//printf("choice1=%d, choice2=%d; ull=%d\n", choice1, choice2, lhs_ull);
		puts("VOLATILE: Messed up &&"); // float doesn't behave as gcc expects it to
	}

	if (f2ull((float) ~((~0ULL) >> 1)) != ~((~0ULL) >> 1)) { /* 0x80000000 */
		puts("Messed up ~~");
	}
	if (d2ull(0.0) != 0LL) {
		puts("Messed up 0.0");
	}
	return 0;
}
