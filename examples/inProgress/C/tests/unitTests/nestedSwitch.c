#include <stdio.h>
int main(void) {
	int inMain = 2;
	for (int i = 0; i < 5; i++) {
		if (i != 4) {
			switch (i) {
			case 1: {
				printf("one\n");
				break;
				}
			case 2:
				printf("two\n");
				break;
			default:
				printf("default\n");
				break;
			case 3:
				printf("three\n");
				break;
			}
		} else {
			printf("sneaky four\n");
		}
	}
	return 0;
}
