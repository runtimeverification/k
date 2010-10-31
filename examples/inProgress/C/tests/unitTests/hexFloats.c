#include <stdio.h> 
int main(void){
	long double x1 = 0x100.abcd12340p2L;
	long double x2 = 0x100.p2;
	long double x3 = 0x1ffp3;
	long double x4 = 0xabc.abcd12340p4F;
	long double x5 = 0x1000.p-2f;
	long double x6 = 0X1.abcd12340P+9l;
	long double x7 = 0x.abcd12340p+11;
	long double x8 = 0x.11p1; // 1/16 + 1/256 == 0.06640625
	
	printf("%d\n", (int)(100 * x1));
	printf("%d\n", (int)(100 * x2));
	printf("%d\n", (int)(100 * x3));
	printf("%d\n", (int)(100 * x4));
	printf("%d\n", (int)(100 * x5));
	printf("%d\n", (int)(100 * x6));
	printf("%d\n", (int)(100 * x7));
	printf("%d\n", (int)(100 * x8));
	// printf("%d\n", (int)x8);
	
	return 0;
}
