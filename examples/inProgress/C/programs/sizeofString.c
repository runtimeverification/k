#include <stdio.h>
int main(void){
	static const unsigned char a[] = "abc";
	static const unsigned char b[3] = "def";
	static const unsigned char c[] = "\065\065";
	static const unsigned char d[] = "ÿ";
	
	printf("sizeof(a) = %d\n", sizeof(a));
	printf("sizeof(b) = %d\n", sizeof(b));
	printf("sizeof(c) = %d\n", sizeof(c));
	printf("sizeof(d) = %d\n", sizeof(d));
	
	return 0;
}
