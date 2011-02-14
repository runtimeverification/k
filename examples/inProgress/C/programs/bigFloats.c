// this test is based on the gcc torture test 920710-1.c
#include <stdio.h>
int main(void) {
	// printf("%llu\n", 18446744073709551615ULL);
	// printf("%f\n", (double)18446744073709551615ULL);
	// printf("%f\n", 1.84467440737095e+19);
	
	if ((double) 18446744073709551615ULL < 1.84467440737095e+19) {
		printf("1\n");
	}
	if ((double) 18446744073709551615ULL > 1.84467440737096e+19) {
		printf("2\n");
	}
	if (16777217L != (float)16777217e0) {
		printf("3\n");
	}
	
	return 0;
}
