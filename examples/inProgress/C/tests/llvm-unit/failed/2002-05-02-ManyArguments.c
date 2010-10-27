
#include <stdio.h>

void printfn(int a, short b, double C, float D, signed char E, char F, void *G, double *H, int I, long long J) {
	printf("%d, %d, %f, %f, %d\n", a, b, C, D, E);
	printf("%d, %ld, %ld, %d, %lld\n", F, (long) G, (long) H, I, J);
}

int main() {
	printfn(12, 2, 123.234, 1231.12312f, -12, 23, (void*)123456, 0, 1234567, 123124124124LL);
	return 0;
}
