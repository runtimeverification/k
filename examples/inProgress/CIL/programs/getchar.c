#include <stdio.h>

int main(void){
	char c;
	puts ("Enter text. Include a dot ('.') in a sentence to exit:");
	do {
		c = getchar();
		putchar (c);
	} while (c != '.');
	puts("");
	return 0;
}
