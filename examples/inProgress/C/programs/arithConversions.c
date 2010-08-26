#include <stdio.h>

// struct {
	// int x : 7;
	// int y : 11;
// } s = { 1, 2 };
// int t = s.x + s.y;

int test1(void){
	unsigned short int a = -12;
	signed short int b = -12;
	printf ("%s\n", (a == b) ? "BUG in 1" : "Good in 1");
	return 0;
}

int test2(void){
	unsigned char a = 5, b = 200;
	unsigned int c = a * b;
	if (c == 1000){
		printf("Good answer in 2\n");
	} else if (c == 232) {
		printf("BUG: No promotions in 2\n");
	} else {
		printf("BUG: Something really weird happened in 2\n");
	}
	return 0;
}

int test3(void){
	int foo = -1;
	unsigned int a = -1;
	printf("%s", a == foo ? "Good in 3_a\n" : "BUG in 3_a\n");
	unsigned char b = -1;
	printf("%s", b == foo ? "BUG in 3_b\n" : "Good in 3_b\n");
	return 0;
}

int main (void) {
	test1();
	test2();
	test3();
	return 0;
}
