#include <stdio.h>
int main(void){

	signed char scl = -127;
	signed char sch = 127;
	unsigned char ucl = 0;
	unsigned char uch = 255U;
	
	short int sil = -32767;
	short int sih = 32767;
	unsigned short int usil = 0;
	unsigned short int usih = 65535U;
	
	int il = -32767;
	int ih = 32767;
	unsigned int uil = 0;
	unsigned int uih = 65535U;
	long int lil = -2147483647L;
	long int lih = 2147483647L;
	unsigned long int ulil = 0UL;
	unsigned long int ulilh = 4294967295UL;
	long long int llil = -9223372036854775807LL;
	long long int llih = 9223372036854775807LL;
	
	if (!(scl < 0)) { printf("Error 1\n"); }
	if (!(sil < 0)) { printf("Error 2\n"); }
	if (!(il < 0)) { printf("Error 3\n"); }
	if (!(lil < 0)) { printf("Error 4\n"); }
	if (!(llil < 0)) { printf("Error 5\n"); }
	
	
	// if (il != (int)(il)) { printf("Error 1\n"); }
	// if (il != (long int)(il)) { printf("Error 2\n"); }
	// if (il != (long long int)(il)) { printf("Error 3\n"); }
	
	// if (lil == (int)(llil)) { printf("Error 4\n"); }
	// if (0 >= (unsigned int)(il)) { printf("Error 5\n"); }
	// if (0 >= (unsigned long int)(lil)) { printf("Error 6\n"); }
	// if (0 >= (unsigned long long int)(llil)) { printf("Error 7\n"); }
		
	
	
	// unsigned long long int ullil = 18446744073709551615ULL;
	// apparently cil doesn't support unsigned long long int
	
	return 0;
}
