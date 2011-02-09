#include <stdio.h>
int main(void){
	char **cpp;
	char *p;
	char c = 'A'; // changed for passing version.  there is another negative test case for failing version
	cpp = &p;
	*cpp = &c;
	printf("**cpp == %c\n", **cpp);
	*p = 0;
	printf("*p == %d\n", *p);
	printf("c == %d\n", c);
	return 0;
}
