#include <stdio.h>
typedef unsigned long long ull;
ull gull;

ull t11 (int n, ull x) {
	while (n--) {
		x += -gull; 
	} 
	return x; 
}

int main(void){
	gull = 100ULL;
	ull tmp;
	ull res;
	
	tmp	= t11(3, 4294967295ULL);
	// tmp = 4294967295 - 300 = 4294966995
	// gull = 100
	// -gull = -100 = 18446744073709551516
	// * 3 = 18446744073709551316
	// + 4294967295ULL = 18446744078004518611
	// 					- 18446744073709551616
	// 					4294966995
	res = ((- gull) * 3ULL) + 4294967295ULL;
	unsigned long long testval = - 100ULL;
	// since our printf isn't technically correct
	printf("VOLATILE: gull=%u, tmp=%u, res=%u\n", gull, tmp, res);
	if (tmp != (testval * 3ULL) + 4294967295ULL) {
		printf("bad 1\n");
	}
	
	tmp	= t11 (3, 0xffffffffULL);
	res = -gull * 3 + 0xffffffffULL;
	printf("VOLATILE: gull=%u, tmp=%u, res=%u\n", gull, tmp, res);
	if (tmp != -gull * 3 + 0xffffffffULL) {
		printf("bad 3\n");
	}
	return 0;
}
