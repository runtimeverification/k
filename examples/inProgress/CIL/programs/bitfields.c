#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
struct bfs {
	unsigned int a0 : 1;
	unsigned int a1 : 1;
	unsigned int a2 : 1;
	unsigned int a3 : 1;
	unsigned int a4 : 1;
	unsigned int a5 : 1;
	unsigned int a6 : 1;
	unsigned int a7 : 1; // boundary
	unsigned int b0 : 2;
	unsigned int b1 : 2;
	unsigned int b2 : 2;
	unsigned int b3 : 2; // boundary
	unsigned int c1 : 4;
	unsigned int c2 : 4; // boundary
	unsigned int d : 8; // boundary
	unsigned int e : 16; // boundary
	unsigned int f : 6;	// 6
	// implicit :2 since next is not a bit field
	unsigned char g;
	unsigned long long h:40;
};
struct bfs s;
struct bfs* p = &s;

int testOnes(void){
	s.a0 = 0;
	s.a1 = 0;
	s.a2 = 0;
	s.a3 = 0;
	s.a4 = 0;
	s.a5 = 0;
	s.a6 = 0;
	s.a7 = 0;
	if (s.a0 != 0){ puts("BUG: a0"); }
	if (s.a1 != 0){ puts("BUG: a0"); }
	if (s.a2 != 0){ puts("BUG: a0"); }
	if (s.a3 != 0){ puts("BUG: a0"); }
	if (s.a4 != 0){ puts("BUG: a0"); }
	if (s.a5 != 0){ puts("BUG: a0"); }
	if (s.a6 != 0){ puts("BUG: a0"); }
	if (s.a7 != 0){ puts("BUG: a0"); }
	s.a0 = 1;
	s.a1 = 1;
	s.a2 = 1;
	s.a3 = 1;
	s.a4 = 1;
	s.a5 = 1;
	s.a6 = 1;
	s.a7 = 1;
	if (s.a0 != 1){ puts("BUG: a1"); }
	if (s.a1 != 1){ puts("BUG: a1"); }
	if (s.a2 != 1){ puts("BUG: a1"); }
	if (s.a3 != 1){ puts("BUG: a1"); }
	if (s.a4 != 1){ puts("BUG: a1"); }
	if (s.a5 != 1){ puts("BUG: a1"); }
	if (s.a6 != 1){ puts("BUG: a1"); }
	if (s.a7 != 1){ puts("BUG: a1"); }
	s.a0 = 1;
	s.a1 = 0;
	s.a2 = 1;
	s.a3 = 1;
	s.a4 = 0;
	s.a5 = 1;
	s.a6 = 1;
	s.a7 = 1;
	if (s.a0 != 1){ puts("BUG: a2"); }
	if (s.a1 != 0){ puts("BUG: a2"); }
	if (s.a2 != 1){ puts("BUG: a2"); }
	if (s.a3 != 1){ puts("BUG: a2"); }
	if (s.a4 != 0){ puts("BUG: a2"); }
	if (s.a5 != 1){ puts("BUG: a2"); }
	if (s.a6 != 1){ puts("BUG: a2"); }
	if (s.a7 != 1){ puts("BUG: a2"); }
	s.a6 = 0;
	if (s.a5 != 1){ puts("BUG: a3"); }
	if (s.a6 != 0){ puts("BUG: a3"); }
	if (s.a7 != 1){ puts("BUG: a3"); }
	unsigned char firstChar = (char)*((char*)&s);
	if (firstChar == 181){
		puts("VOLATILE: top bits are MSB");
		puts("byte interp OK");
	} else if (firstChar == 173) {
		puts("VOLATILE: top bits are LSB");
		puts("byte interp OK");
	} else {
		puts("BUG: a4");
	}
	p->a6 = 1;
	if (p->a5 != 1){ puts("BUG: a5"); }
	if (p->a6 != 1){ puts("BUG: a5"); }
	if (p->a7 != 1){ puts("BUG: a5"); }
	p->a5 = 0;
	p->a7 = 0;
	p->a6 = (unsigned int)15;
	if (p->a5 != 0){ puts("BUG: a6"); }
	if (p->a6 != 1){ puts("BUG: a6"); }
	if (p->a7 != 0){ puts("BUG: a6"); }
	return 0;
}

int testTwos(){
	s.b0 = 0;
	s.b1 = 0;
	s.b2 = 0;
	s.b3 = 0;
	if (s.b0 != 0){ puts("BUG: b0"); }
	if (s.b1 != 0){ puts("BUG: b0"); }
	if (s.b2 != 0){ puts("BUG: b0"); }
	if (s.b3 != 0){ puts("BUG: b0"); }
	s.b0 = 1;
	s.b1 = 1;
	s.b2 = 1;
	s.b3 = 1;
	if (s.b0 != 1){ puts("BUG: b1"); }
	if (s.b1 != 1){ puts("BUG: b1"); }
	if (s.b2 != 1){ puts("BUG: b1"); }
	if (s.b3 != 1){ puts("BUG: b1"); }
	s.b0 = 2;
	s.b1 = 2;
	s.b2 = 2;
	s.b3 = 2;
	if (s.b0 != 2){ puts("BUG: b2"); }
	if (s.b1 != 2){ puts("BUG: b2"); }
	if (s.b2 != 2){ puts("BUG: b2"); }
	if (s.b3 != 2){ puts("BUG: b2"); }
	s.b0 = 1;
	s.b1 = 0;
	s.b2 = 2;
	s.b3 = 3;
	if (s.b0 != 1){ puts("BUG: b3"); }
	if (s.b1 != 0){ puts("BUG: b3"); }
	if (s.b2 != 2){ puts("BUG: b3"); }
	if (s.b3 != 3){ puts("BUG: b3"); }
	s.b0 = 3;
	s.b1 = 2;
	s.b2 = 0;
	s.b3 = 1;
	if (s.b0 != 3){ puts("BUG: b4"); }
	if (s.b1 != 2){ puts("BUG: b4"); }
	if (s.b2 != 0){ puts("BUG: b4"); }
	if (s.b3 != 1){ puts("BUG: b4"); }
	// 11 10 00 01 => 10000111
	// 01 00 10 11 => 01001011
	unsigned char firstChar = (char)*(((char*)&(s))+1);
	if (firstChar == 135){
		puts("VOLATILE: top bits are MSB");
		puts("byte interp OK");
	} else if (firstChar == 75) {
		puts("VOLATILE: top bits are LSB");
		puts("byte interp OK");
	} else {
		printf("BUG: b5: %d\n", firstChar);
	}
	p->b2 = 3;
	if (p->b1 != 2){ puts("BUG: b6"); }
	if (p->b2 != 3){ puts("BUG: b6"); }
	if (p->b3 != 1){ puts("BUG: b6"); }
	return 0;
}

int testEights(void){
	s.d = 183;
	if (s.d != 183){ puts("BUG: d0"); }
	s.d = 75;
	if (s.d != 75){ puts("BUG: d1"); }

	unsigned char firstChar = (char)*(((char*)&(s))+3);
	if (firstChar == 75){
		puts("byte interp OK");
	} else {
		printf("BUG: d2: %d\n", firstChar);
	}
	p->d = 112;
	if (p->d != 112){ puts("BUG: d3"); }
	return 0;
}

int testSixteens(void){
	s.e = (unsigned int)30203;
	
	if (s.e != (unsigned int)30203){ puts("BUG: e0"); }
	s.e = (unsigned int)23213;
	if (s.e != (unsigned int)23213){ puts("BUG: e1"); }

	uint16_t firstChar = (uint16_t)*((uint16_t*)(((char*)&(s))+4));
	if (firstChar == 23213){
		puts("short interp OK");
	} else {
		printf("BUG: e2: %d\n", firstChar);
	}
	p->e = 11606;
	if (p->e != 11606){ puts("BUG: e3"); }
	return 0;
}

int testPartial(void){
	s.f = 45;
	s.g = 145;
	if (s.f != 45){ puts("BUG: f0"); }
	if (s.g != 145){ puts("BUG: f0"); }
	s.g = 75;
	if (s.f != 45){ puts("BUG: f1"); }
	if (s.g != 75){ puts("BUG: f1"); }	
	s.f = 21;
	if (s.f != 21){ puts("BUG: f2"); }
	if (s.g != 75){ puts("BUG: f2"); }
	
	unsigned char firstChar = *(&(s.g));
	if (firstChar == 75){
		puts("ok");
	} else {
		printf("BUG: e3: %d\n", firstChar);
	}
	p->g = 119;
	if (p->g != 119){ puts("BUG: f4"); }
	return 0;
}

// int testForty(void){
	// s.h = 0x0100;
	// if (s.h != 0x0100){ puts("BUG: h0"); }
	// unsigned long long result = s.h<<32;

	// if (result != 0){ printf("BUG: h1: result = %llu\n", result); }
	// return 0;
// }
	
int main(void){
	testOnes();
	testTwos();
	testEights();
	testSixteens();
	testPartial();
	//testForty();
	return 0;
}
