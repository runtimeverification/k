#include <stdio.h>

int main(void){
	const char **cpp;
	char *p;
	const char c = 'A';
	cpp = &p; // constraint violation, should not execute
	*cpp = &c;
	*p = 0;
	return 0;
}
