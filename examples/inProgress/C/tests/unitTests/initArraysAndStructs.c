#include <stdio.h>
int main(void) {
	struct {int a; int b;} s[] = {[4] = 5, 6, 0, 8};
	s[5].a = s[4].b;
	printf("[4].a=%d, [4].b=%d, [5].a=%d, [5].b=%d\n", s[4].a, s[4].b, s[5].a, s[5].b);
	printf("sizeof(s)/sizeof(s[0]) = %d\n", sizeof(s)/sizeof(s[0]));
	return 0;
}
