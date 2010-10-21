#include <stdio.h>

int mysub1 (unsigned long long i) {
	if (i < 2147483647+1) { puts("first"); }
	if (i < 2147483648) { puts("second"); }
}
int mysub2 (unsigned int i) {
	if (i + 0x80000000) { puts("third"); }
	if (i + 2147483648) { puts("fourth"); }
}
int main(void) {
	mysub1(0x80000000);
	mysub2(0x80000000);
	
	int* p = (int[]) {2, 4};
	
	return 0;
}
