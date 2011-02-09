#include <stdio.h>

struct v {
	union {
		struct { int i, j; };
		struct { long k, l; } w;
	};
	int m;
} v1;

int main(void){
	v1.i = 2;
	printf("%d\n", v1.i);
	// v1.k = 3; // invalid: inner structure is not anonymous
	v1.w.k = 5;
	printf("%d\n", v1.w.k);
	return 0;
}
