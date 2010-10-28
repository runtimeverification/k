#include <stdio.h>
struct {
	int a : 4;
	int b : 4;
	unsigned int c : 1;
	int d : 2;
	int e : 2;
	int f : 10;
	int g : 10;
} s;

int main(void){
	s.a = 6;
	s.b = -8;
	s.c = 1;
	s.d = 1;
	s.e = -2;
	s.f = 312;
	s.g = -405;
	
	printf("%d\n", s.a);
	printf("%d\n", s.b);
	printf("%d\n", s.c);
	printf("%d\n", s.d);
	printf("%d\n", s.e);
	printf("%d\n", s.f);
	printf("%d\n", s.g);

	return 0;
}
