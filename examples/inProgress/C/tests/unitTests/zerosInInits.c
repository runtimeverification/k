#include <stdlib.h>
int main(void){
	char a1[3] = {1};
	float a2[3] = {1.0, 2};
	int* a3[3] = {(int*)&a1[3]};
	int a4[3] = {1};
	struct {int a; int* b; int c[2]; struct { int* da; } d;} a5 = {1, .c[1]=1};
	
	if (a1[0] != 1) { return 1; }
	if (a1[1] != 0) { return 2; }
	if (a1[2] != (unsigned char)0) { return 3; }
	
	if (a2[0] != 1) { return 4; }
	if (a2[1] != 2.0) { return 5; }
	if (a2[2] != 0) { return 6; }
	
	if (a3[0] != (int*)(long long int)&a1[3]) { return 7; }
	if (a3[1] != 0) { return 8; }
	if (a3[2] != NULL) { return 9; }
	
	if (a4[0] != 1) { return 10; }
	if (a4[1] != 0) { return 11; }
	if (a4[2] != (char)0) { return 12; }
	
	if (a2[0] != (float)1) { return 13; }
	if (a2[1] != (float)2) { return 14; }
	if (a2[2] != 0.0) { return 15; }
	
	
	if (a5.a != (float)1) { return 16; }
	if (a5.a != 1) { return 17; }
	
	if (a5.b != NULL) { return 18; }
	if (a5.b != 0) { return 19; }
	
	if (a5.c[0] != 0.0) { return 21; }
	if (a5.c[0] != 0) { return 22; }
	if (a5.c[1] != 1) { return 23; }
	
	if (a5.d.da != NULL) { return 24; }
	if (a5.d.da != 0) { return 25; }
	
	return 0;	
}
