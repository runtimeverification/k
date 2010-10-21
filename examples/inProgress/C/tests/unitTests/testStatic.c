#include <stdio.h>
int x = 17;
int y = 5;
int f(void){
	static int x;
	int y;
	x++;
	{
		static int x; 
		x = x + 2;
		y = x;
	}
	
	return y * 2 + x * 3;
}

int g(void){
	static int x;
	x++;
	return x;
}

int main(void){
	int x = 5;
	printf("01y=%d\n", y);
	int y = 6;
	printf("02y=%d\n", y);
	{
		extern int y;
		printf("03y=%d\n", y);
	}
	printf("04y=%d\n", y);
	f();f();
	g();g();g();
	return f() + g();
}
