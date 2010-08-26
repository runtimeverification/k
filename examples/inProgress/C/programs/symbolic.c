#include <stdlib.h>
#include <stdio.h>

int main(void) {
	unsigned char unknownChar;
	unsigned short unknownShort;
	struct point {
		int x;
		int y;
	} unknownPoint;
	
	unsigned char otherChar = unknownChar;
	unsigned short otherShort = unknownShort;
	struct point otherPoint = unknownPoint;
	
	if (otherChar != unknownChar) {
		puts("otherChar != unknownChar");
	}
	otherChar <<= 8;
	if (otherChar != 0) {
		puts("otherChar != 0");
	}
	unknownChar |= 16;  // ???1 ????
	unknownChar <<= 3;
	unknownChar >>= 7;
	if (unknownChar != 1) {
		puts("unknownChar != 1");
	}
	if (otherShort != unknownShort) {
		puts("otherShort != unknownShort");
	}
	if (otherPoint.x != unknownPoint.x){
		puts("otherPoint.x != unknownPoint.x");
	}
	if (otherPoint.y != unknownPoint.y){
		puts("otherPoint.y != unknownPoint.y");
	}
	return 0;
}
