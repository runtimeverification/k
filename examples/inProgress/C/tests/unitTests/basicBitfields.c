#include <stdio.h>
struct {
	unsigned int x1 : 1;
	unsigned int x2 : 2;
	unsigned int x3 : 3;
	int y;
} s;
int main(void){
	s.y = 7;
	
	s.x2 = 2;
	s.x1 = 1;
	s.x3 = 3;
		
	printf("%d\n", s.x2);
	printf("%d\n", s.x1);
	printf("%d\n", s.x3);
	printf("%d\n", s.y);
	return 0;
}
