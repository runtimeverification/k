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
	unsigned int : 0;
	unsigned int i : 13; // boundary
	unsigned int j : 3;
	unsigned int : 0 ;
	unsigned int k : 11;
	unsigned int : 0 ;
	unsigned char g;
	// unsigned long long h:40;
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
	if (s.a0 != 0){ printf("BUG: a0\n"); }
	if (s.a1 != 0){ printf("BUG: a0\n"); }
	if (s.a2 != 0){ printf("BUG: a0\n"); }
	if (s.a3 != 0){ printf("BUG: a0\n"); }
	if (s.a4 != 0){ printf("BUG: a0\n"); }
	if (s.a5 != 0){ printf("BUG: a0\n"); }
	if (s.a6 != 0){ printf("BUG: a0\n"); }
	if (s.a7 != 0){ printf("BUG: a0\n"); }
	s.a0 = 1;
	s.a1 = 1;
	s.a2 = 1;
	s.a3 = 1;
	s.a4 = 1;
	s.a5 = 1;
	s.a6 = 1;
	s.a7 = 1;
	if (s.a0 != 1){ printf("BUG: a1\n"); }
	if (s.a1 != 1){ printf("BUG: a1\n"); }
	if (s.a2 != 1){ printf("BUG: a1\n"); }
	if (s.a3 != 1){ printf("BUG: a1\n"); }
	if (s.a4 != 1){ printf("BUG: a1\n"); }
	if (s.a5 != 1){ printf("BUG: a1\n"); }
	if (s.a6 != 1){ printf("BUG: a1\n"); }
	if (s.a7 != 1){ printf("BUG: a1\n"); }
	s.a0 = 1;
	s.a1 = 0;
	s.a2 = 1;
	s.a3 = 1;
	s.a4 = 0;
	s.a5 = 1;
	s.a6 = 1;
	s.a7 = 1;
	if (s.a0 != 1){ printf("BUG: a2\n"); }
	if (s.a1 != 0){ printf("BUG: a2\n"); }
	if (s.a2 != 1){ printf("BUG: a2\n"); }
	if (s.a3 != 1){ printf("BUG: a2\n"); }
	if (s.a4 != 0){ printf("BUG: a2\n"); }
	if (s.a5 != 1){ printf("BUG: a2\n"); }
	if (s.a6 != 1){ printf("BUG: a2\n"); }
	if (s.a7 != 1){ printf("BUG: a2\n"); }
	s.a6 = 0;
	if (s.a5 != 1){ printf("BUG: a3\n"); }
	if (s.a6 != 0){ printf("BUG: a3\n"); }
	if (s.a7 != 1){ printf("BUG: a3\n"); }
	// printf("VOLATILE: ");
	// printf("%d", s.a0);
	// printf("%d", s.a1);
	// printf("%d", s.a2);
	// printf("%d", s.a3);
	// printf("%d", s.a4);
	// printf("%d", s.a5);
	// printf("%d", s.a6);
	// printf("%d\n", s.a7);
	unsigned char firstChar = (char)*((char*)&s);
	if (firstChar == 181){
		//printf("VOLATILE: top bits are MSB\n");
		printf("byte interp OK\n");
	} else if (firstChar == 173) {
		//printf("VOLATILE: top bits are LSB\n");
		printf("byte interp OK\n");
	} else {
		printf("BUG: a4: %d\n", firstChar);
	}
	p->a6 = 1;
	if (p->a5 != 1){ printf("BUG: a5\n"); }
	if (p->a6 != 1){ printf("BUG: a5\n"); }
	if (p->a7 != 1){ printf("BUG: a5\n"); }
	p->a5 = 0;
	p->a7 = 0;
	p->a6 = (unsigned int)15;
	if (p->a5 != 0){ printf("BUG: a6\n"); }
	if (p->a6 != 1){ printf("BUG: a6\n"); }
	if (p->a7 != 0){ printf("BUG: a6\n"); }
	return 0;
}

int testTwos(){
	s.b0 = 0;
	s.b1 = 0;
	s.b2 = 0;
	s.b3 = 0;
	if (s.b0 != 0){ printf("BUG: b0\n"); }
	if (s.b1 != 0){ printf("BUG: b0\n"); }
	if (s.b2 != 0){ printf("BUG: b0\n"); }
	if (s.b3 != 0){ printf("BUG: b0\n"); }
	s.b0 = 1;
	s.b1 = 1;
	s.b2 = 1;
	s.b3 = 1;
	if (s.b0 != 1){ printf("BUG: b1\n"); }
	if (s.b1 != 1){ printf("BUG: b1\n"); }
	if (s.b2 != 1){ printf("BUG: b1\n"); }
	if (s.b3 != 1){ printf("BUG: b1\n"); }
	s.b0 = 2;
	s.b1 = 2;
	s.b2 = 2;
	s.b3 = 2;
	if (s.b0 != 2){ printf("BUG: b2\n"); }
	if (s.b1 != 2){ printf("BUG: b2\n"); }
	if (s.b2 != 2){ printf("BUG: b2\n"); }
	if (s.b3 != 2){ printf("BUG: b2\n"); }
	s.b0 = 1;
	s.b1 = 0;
	s.b2 = 2;
	s.b3 = 3;
	if (s.b0 != 1){ printf("BUG: b3\n"); }
	if (s.b1 != 0){ printf("BUG: b3\n"); }
	if (s.b2 != 2){ printf("BUG: b3\n"); }
	if (s.b3 != 3){ printf("BUG: b3\n"); }
	s.b0 = 3;
	s.b1 = 2;
	s.b2 = 0;
	s.b3 = 1;
	if (s.b0 != 3){ printf("BUG: b4\n"); }
	if (s.b1 != 2){ printf("BUG: b4\n"); }
	if (s.b2 != 0){ printf("BUG: b4\n"); }
	if (s.b3 != 1){ printf("BUG: b4\n"); }
	// 11 10 00 01 => 11100001
	// 11 10 00 01 => 10000111
	// 01 00 10 11 => 01001011
	// 01 00 10 11 => 11100001
	unsigned char firstChar = (char)*(((char*)&(s))+1);
	if (firstChar == 135 || firstChar == 75 || firstChar == 225){
		// printf("VOLATILE: top bits are MSB\n");
		//printf("byte interp OK\n");
	//} else if (firstChar == 75) {
		// printf("VOLATILE: top bits are LSB\n");
		printf("byte interp OK\n");
	//} else if (firstChar == 225) {
	} else {
		printf("BUG: b5: %d\n", firstChar);
	}
	p->b2 = 3;
	if (p->b1 != 2){ printf("BUG: b6\n"); }
	if (p->b2 != 3){ printf("BUG: b6\n"); }
	if (p->b3 != 1){ printf("BUG: b6\n"); }
	return 0;
}

int testEights(void){
	s.d = 183;
	if (s.d != 183){ printf("BUG: d0\n"); }
	s.d = 75;
	if (s.d != 75){ printf("BUG: d1\n"); }

	unsigned char firstChar = (char)*(((char*)&(s))+3);
	if (firstChar == 75){
		printf("byte interp OK\n");
	} else {
		printf("BUG: d2: %d\n", firstChar);
	}
	p->d = 112;
	if (p->d != 112){ printf("BUG: d3\n"); }
	return 0;
}

int testSixteens(void){
	s.e = (unsigned int)30203;
	
	if (s.e != (unsigned int)30203){ printf("BUG: e0\n"); }
	s.e = (unsigned int)23213;
	if (s.e != (unsigned int)23213){ printf("BUG: e1\n"); }

	uint16_t firstChar = (uint16_t)*((uint16_t*)(((char*)&(s))+4));
	if (firstChar == 23213 || firstChar == 44378){ // bitfields don't have to work like normal types
		printf("short interp OK\n");
	} else {
		printf("BUG: e2: %d\n", firstChar);
	}
	p->e = 11606;
	if (p->e != 11606){ printf("BUG: e3\n"); }
	return 0;
}

int testPartial(void){
	s.f = 45;
	s.g = 145;
	if (s.f != 45){ printf("BUG: f0\n"); }
	if (s.g != 145){ printf("BUG: f0\n"); }
	s.g = 75;
	if (s.f != 45){ printf("BUG: f1\n"); }
	if (s.g != 75){ printf("BUG: f1\n"); }	
	s.f = 21;
	if (s.f != 21){ printf("BUG: f2\n"); }
	if (s.g != 75){ printf("BUG: f2\n"); }
	
	unsigned char firstChar = *(&(s.g));
	if (firstChar == 75){
		printf("ok\n");
	} else {
		printf("BUG: e3: %d\n", firstChar);
	}
	p->g = 119;
	if (p->g != 119){ printf("BUG: f4\n"); }
	return 0;
}

int testBigPartial(void){
	s.i = 45;
	s.j = 2;
	if (s.i != 45){ printf("BUG: i0a : %d\n", s.i); }
	if (s.j != 2){ printf("BUG: i0b : %d\n", s.j); }
	s.j = 7;
	if (s.i != 45){ printf("BUG: i1a : %d\n", s.i); }
	if (s.j != 7){ printf("BUG: i1b : %d\n", s.j); }	
	s.i = 3073;
	if (s.i != 3073){ printf("BUG: i2a : %d\n", s.i); }
	if (s.j != 7){ printf("BUG: i2b : %d\n", s.j); }
	
	// unsigned char firstChar = *(&(s.j));
	// if (firstChar == 75){
		// printf("ok\n");
	// } else {
		// printf("BUG: i3: %d\n", firstChar);
	// }
	p->i = 2000;
	if (p->i != 2000){ printf("BUG: i4 : %d, %d\n", p->i, s.i); }
	return 0;
}


int testJustBigPartial(void){
	s.k = 45;
	if (s.k != 45){ printf("BUG: k0 : %d\n", s.k); }
	s.k = 7;
	if (s.k != 7){ printf("BUG: k1 : %d\n", s.k); }	
	s.k = 1137;
	if (s.k != 1137){ printf("BUG: k2 : %d\n", s.k); }
	s.k = 601;
	if (s.k != 601){ printf("BUG: k3 : %d\n", s.k); }
	
	// unsigned char firstChar = *(&(s.j));
	// if (firstChar == 75){
		// printf("ok\n");
	// } else {
		// printf("BUG: i3: %d\n", firstChar);
	// }
	p->k = 1025;
	if (p->k != 1025){ printf("BUG: k4 : %d, %d\n", p->k, s.k); }
	return 0;
}

// int testForty(void){
	// s.h = 0x0100;
	// if (s.h != 0x0100){ printf("BUG: h0"); }
	// unsigned long long result = s.h<<32;

	// if (result != 0){ printf("BUG: h1: result = %llu\n", result); }
	// return 0;
// }
	
int main(void){
	testOnes();
	printf("finished ones\n");
	testTwos();
	printf("finished twos\n");
	testEights();
	printf("finished eights\n");
	testSixteens();
	printf("finished sixteens\n");
	testPartial();
	printf("finished partial\n");
	testJustBigPartial();
	printf("finished just big partial\n");
	testBigPartial();
	printf("finished big partial\n");
	//testForty();
	return 0;
}
