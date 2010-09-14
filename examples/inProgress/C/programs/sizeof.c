#include <stdio.h>

struct s0 {
	char* z;
	char a;
	short int b;
	int c;
	long int d;
	long long int e;
};

struct s1 {
	char f[5];
	struct s0 g;
	struct s0 h[5];
	struct s0 *i;
};

int main(void){
	char tchar;
	unsigned char tuchar;
	signed char tschar;
	
	short int tsint;
	unsigned short int tusint;
	
	int tint;
	unsigned int tuint;
	
	long int tlint;
	unsigned long int tulint;
	
	long long int tllint;
	unsigned long long int tullint;
	
	int* tpint;
	
	if (sizeof(tchar) != 1 || sizeof(tuchar) != 1 || sizeof(tschar) != 1){ printf("Error: 00\n"); }	
	if (sizeof(tchar) > sizeof(tsint) 
		|| sizeof(tchar) > sizeof(tint) 
		|| sizeof(tchar) > sizeof(tlint)
		|| sizeof(tchar) > sizeof(tllint)
		){ printf("Error: 01\n"); }	
	
	if (sizeof(tsint) > sizeof(tint) 
		|| sizeof(tsint) > sizeof(tlint) 
		|| sizeof(tsint) > sizeof(tllint)
		){ printf("Error: 03\n"); }	
	if (sizeof(tusint) != sizeof(tsint)){ printf("Error: 04\n"); }
	if (sizeof(tsint) < 2){ printf("Error: 05\n"); }
	
	if (sizeof(tint) != sizeof(tuint)){ printf("Error: 07\n"); }
	if (sizeof(tint) < 2){ printf("Error: 08\n"); }
	if (sizeof(tint) > sizeof(tlint) || sizeof(tint) > sizeof(tllint)){ printf("Error: 09\n"); }	
	
	if (sizeof(tlint) != sizeof(tulint)){ printf("Error: 10\n"); }
	if (sizeof(tlint) < 4){ printf("Error: 11\n"); }
	if (sizeof(tlint) > sizeof(tllint) ){ printf("Error: 12\n"); }
	
	if (sizeof(tllint) != sizeof(tullint)){ printf("Error: 13\n"); }
	if (sizeof(tllint) < 8){ printf("Error: 14\n"); }
	
	char x[15];
	if (sizeof(x) != 15){ printf("Error: 15\n"); }
	int y[15];
	if (sizeof(y) != 15 * sizeof(int)){ printf("Error: 16\n"); }
	if (sizeof(y) <= sizeof(x)){ printf("Error: 17\n"); }
	//int len = 5;
	// int z[len];
	// if (sizeof(z) != len * sizeof(int)){ printf("Error: 18\n"); }
	
	int w[5][4][3];
	if (sizeof(w) != sizeof(w[1]) * 5){ printf("Error: 19\n"); }
	if (sizeof(w) != sizeof(w[2][1]) * 5 * 4){ printf("Error: 20\n"); }
	if (sizeof(w) != sizeof(w[3][2][1]) * 5 * 4 * 3){ printf("Error: 21a\n"); }
	if (sizeof(w) != sizeof(int[5][4][3])){ printf("Error: 21b\n"); }
	if (sizeof(w[1]) != sizeof(int[4][3])){ printf("Error: 22\n"); }
	if (sizeof(w[2][3]) != sizeof(int[3])){ printf("Error: 23\n"); }
	if (sizeof(w[2][3][0]) != sizeof(int)){ printf("Error: 24a\n"); }
	if (sizeof(w[5][4][3]) == sizeof(int[5][4][3])){ printf("Error: 24b\n"); }
	
	if (sizeof(struct s0) < sizeof(char*) + sizeof(char) + sizeof(short int) + sizeof(int) + sizeof(long int) + sizeof(long long int)) { printf("Error: 25\n"); }
	if (sizeof(struct s1) < sizeof(char[5]) + sizeof(struct s0) + sizeof(struct s0) * 5 + sizeof(struct s0*)) { printf("Error: 26\n"); }

	struct s0 mys0;
	struct s1 mys1;
	struct s1 mys1b[7];
	
	if (sizeof(struct s0) < sizeof(mys0.z) + sizeof(mys0.a) + sizeof(mys0.b) + sizeof(mys0.c) + sizeof(mys0.d) + sizeof(mys0.e)) { printf("Error: 27\n"); }
	if (sizeof(struct s1) < sizeof(mys1.f) + sizeof(mys1.g) + sizeof(mys1.h) + sizeof(mys1.i)) { printf("Error: 28\n"); }
	
	if (sizeof(mys1b) != sizeof(struct s1) * 7) { printf("Error: 29\n"); }

	if ((char*)&mys1b[3] != (char*)&mys1b + sizeof(struct s1) * 3) { printf("Error: 30\n"); }
	
	//if (sizeof(mys1b) != sizeof((struct s1[7])tpint)) { printf("Error 31\n"); }
	// printf("sizeof(char) = %d\n", sizeof(char));
	// printf("sizeof(short int) = %d\n", sizeof(short int));
	// printf("sizeof(int) = %d\n", sizeof(int));
	// printf("sizeof(long int) = %d\n", sizeof(long int));
	// printf("sizeof(long long int) = %d\n", sizeof(long long int));
	// printf("sizeof(int*) = %d\n", sizeof(int*));
	// printf("sizeof(struct s0) = %d\n", sizeof(struct s0));
	
	return 0;
}
