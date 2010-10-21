#include <stdio.h>
int main(void) {
	int inMain = 2;
	for (int i = 0; i < 5; i++) {
		if (i != 4) {
			while (i == 1) {
				printf("one\n");
				break;
			}
			while (i == 2) {
				printf("two\n");
				break;
			}
			while (i == 3) {
				printf("three\n");
				break;
			}
		} else {
			printf("sneaky four\n");
		}
	}
	return 0;
}
