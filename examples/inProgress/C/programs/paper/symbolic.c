#include <stdio.h>
int main(void) {
	struct _s { int a[5]; int b[5]; } s;
	if (&s.a < &s.b) {
		printf("in order\n");
	} else {
		printf("backwards\n");
	}
	return 0;
}


// int main(void) {
	// int a[5], b[5];
	// if (&a < &b) {
		// printf("in order\n");
	// } else {
		// printf("backwards\n");
	// }
	// return 0;
// }
