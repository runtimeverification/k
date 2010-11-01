#include <stdio.h>

struct bigstruct {
	int a;
	int b;
	int c;
	int* p;
	int d;
	int e;
	int f;
	struct bigstruct* this;
} ;

int main(void){
	int x = 1;
	int* p = &x;
	int** pp = &p;
	int* ap[] = {p, p};
	int** app = ap;
	int data[] = {1, 0};
	x++; // x == 2
	(*p)++; // x == 3
	(**pp)++; // x == 4;
	//int* q = ap[1];
	(**(ap + data[0]))++; // x == 5;
	(*(ap[data[1]]))++; // x == 6;
	
	struct bigstruct s;
	struct bigstruct* ps = &s;
	s.a = 1;
	s.b = 2;
	s.c = 3;
	s.d = 4;
	s.e = 5;
	s.f = 6;
	s.p = &(s.b);
	s.this = &s;
	x += *((s.this)->p); // x == 8;
	x += s.b + s.e + s.f; // x == 21;
	(*((s.this)->p)) ++; // s.b == 3;
	x += (&s)->b; // x == 24
	
	static const int pad[64] = {
	0x80, 5, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
    };
	x += pad[pad[1]]; // x == 26
	
	static const char *const arrayOfStrings[7*2] = {
		"", "d41d8cd98f00b204e9800998ecf8427e",
		"a", "0cc175b9c0f1b6a831c399e269772661",
		"abc", "900150983cd24fb0d6963f7d28e17f72",
		"message digest", "f96b697d7cb7938d525a2f31aaf161d0",
		"abcdefghijklmnopqrstuvwxyz", "c3fcd3d76192e4007dfb496cca67e13b",
		"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789",
					"d174ab98d277d9f5a5611c2c9f419d9f",
		"12345678901234567890123456789012345678901234567890123456789012345678901234567890", "57edf4a22be3c955ac49da2e2107b67a"
	    };
	
	if (arrayOfStrings[1][0] == 'd'){
		x++; // x == 27
	}
	
	int (*fpArray[])(void)  = {main, main, main, main, main, main, main, main, main, main, main, main};
	
	int multidem[2][2][2];
	multidem[0][0][0] = 1;
	multidem[0][0][1] = 2;
	multidem[0][1][0] = 3;
	multidem[0][1][1] = 4;
	multidem[1][0][0] = 5;
	multidem[1][0][1] = 6;
	multidem[1][1][0] = 7;
	multidem[1][1][1] = 8;
	
	for (int i = 0; i < 2; i++){
		for (int j = 0; j < 2; j++){
			for (int kk = 0; kk < 2; kk++){
				x += multidem[i][j][kk]; // x += 36, x == 63
			}
		}
	}
	
	int y = 0;
	x += (y++, y += 3, ++y); // x += 5, x == 68
	
	
	printf("%d\n",x);
	return x;
}
