#include <stdio.h>

int x;
int y = 5;

struct {
	int x;
	int y;
} pt;

struct {
	int x;
	int y;
} pair = {2, 3} ;

union {
	char x;
	int y;
} un;

union {
	char x;
	int y;
} un2 = {'x'};

int arr[5];

int main(void){
	if (x != 0){ puts("x != 0\n"); }
	if (y != 5){ puts("y != 5\n"); }
	
	if (pt.x != 0){ puts("pt.x != 0\n"); }
	if (pt.y != 0){ puts("pt.y != 0\n"); }
	
	if (pair.x != 2){ puts("pair.x != 2\n"); }
	if (pair.y != 3){ puts("pair.y != 3\n"); }
	
	if (un.x != 0){ puts("un.x != 0\n"); }
	if (un2.x != 'x'){ puts("un2.x != 'x'\n"); }
	
	if (arr[0] != 0){ puts("arr[0] != 0\n"); }
	
	return 0;
}
