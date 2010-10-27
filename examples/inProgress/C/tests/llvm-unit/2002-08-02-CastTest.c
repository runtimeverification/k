#include <stdio.h>

unsigned test(unsigned X) {
  return (unsigned char)X;
}

int main() {
	printf("%d\n", test(123456));
        return 0;
}

