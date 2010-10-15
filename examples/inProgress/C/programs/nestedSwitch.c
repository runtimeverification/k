#include <stdio.h>
int main(void) {
	for (int i = 0; i < 5; i++) {
		if (i != 4) {
			switch (i) {
			case 1: {
				puts("one");
				break;
				}
			case 2:
				puts("two");
				break;
			default:
				puts("default");
				break;
			case 3:
				puts("three");
				break;
			}
		} else {
			puts("sneaky four");
		}
	}
	return 0;
}
