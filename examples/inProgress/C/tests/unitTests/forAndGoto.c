#include <stdio.h>
int main(void) {
	int inMain = 2;
	for (int i = 0; i < 5; i++) {
		if (i != 4) {
			if (i == 1) {
				goto one;
				one:
				printf("one\n");
			}
			while (i == 2) {
				goto two;
				two:
				printf("two\n");
				break;
			}
		} else {
			printf("sneaky four\n");
		}
	}
	return 0;
}
