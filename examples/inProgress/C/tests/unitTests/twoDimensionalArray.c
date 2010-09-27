//#include <stdio.h>
int main(void) {
	// typedef int intPairs[2];
	// intPairs a[3];
	
	//int b[1][2][3];
	// arrayType(arrayType(arrayType(int, 1), 2), 3)
	// should be arrayType()
	int a[3][2];
	
	a[0][0] = 5;
	a[0][1] = 6;
	a[1][0] = 7;
	a[1][1] = 8;
	a[2][0] = 9;
	a[2][1] = 10;
	
	if (a[0][0] != 5) { return 5; }
	if (a[0][1] != 6) { return 6; }
	if (a[1][0] != 7) { return 7; }
	if (a[1][1] != 8) { return 8; }
	if (a[2][0] != 9) { return 9; }
	if (a[2][1] != 10) { return 10; }
	
	// printf("len(a)==%d, len(a[0])==%d\n", sizeof(a)/sizeof(a[0]), sizeof(a[0])/sizeof(a[0][0]));
	// printf("len(b)==%d, len(b[0])==%d\n", sizeof(b)/sizeof(b[0]), sizeof(b[0])/sizeof(b[0][0]));
	return 0;
}
