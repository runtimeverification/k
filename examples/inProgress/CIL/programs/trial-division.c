/* Copyright (c) 2010 the authors listed at the following URL, and/or
the authors of referenced articles or incorporated external code:
http://en.literateprograms.org/Trial_division_(C)?action=history&offset=20090108114236

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

Retrieved from: http://en.literateprograms.org/Trial_division_(C)?oldid=15839
*/

#include <math.h>  /* For sqrt() */
#include <stdlib.h>   /* for malloc, calloc, free */
#include <string.h>
#include <stdio.h>

#define IS_PRIME 0


unsigned int trial_division_sqrt(unsigned int n) {
    unsigned int sqrt_n = (unsigned int)sqrt((double)n);
    unsigned int x;
    for(x=2; x <= sqrt_n; x++) {
        if ((n % x) == 0) {
            return x;
        }
    }
    return IS_PRIME;
}


unsigned int trial_division_squaring(unsigned int n) {
    unsigned int x, x_squared;
    for(x=2, x_squared=4;
        x_squared > 2*x - 1 && x_squared <= n;
        x++, x_squared += 2*x - 1)
    {
        if ((n % x) == 0) {
            return x;
        }
    }
    return IS_PRIME;
}


unsigned int trial_division_odd(unsigned int n) {
    unsigned int sqrt_n = (unsigned int)sqrt((double)n);
    unsigned int x;
    if ((n % 2) == 0) return 2;
    for(x=3; x <= sqrt_n; x+=2) {
        if ((n % x) == 0) {
            return x;
        }
    }
    return IS_PRIME;
}


typedef unsigned short u16;
typedef unsigned int u32;

u16* primes;

void generate_prime_list(int max) {
    unsigned char* is_not_prime = (unsigned char*)calloc(max+1, 1);
    int i, j, num_primes = 1;
    for(i = 2; i <= max; i++) {
        if (!is_not_prime[i]) {
	        num_primes++;
	        for(j = i + i; j <= max; j += i) {
	            is_not_prime[j] = 1;
	        }
		}
    }
    primes = (u16*)malloc(sizeof(u16) * (num_primes + 1));
    j = 0;
    for(i = 2; i <= max; i++) {
        if (!is_not_prime[i]) {
            primes[j] = i;
            j++;
        }
    }
    primes[j] = 0;
    free(is_not_prime);
}


u32 trial_division_primes(u32 n) {
    u32 sqrt_n = (u32)sqrt((double)n);
    u16* prime = primes;
    while (*prime != 0 && *prime <= sqrt_n) {
        if ((n % *prime) == 0) {
            return *prime;
        }
        prime++;
    }
    return IS_PRIME;
}


int main(void) {
    int i;
	int n;
	//generate_prime_list(65536);
	generate_prime_list(128);
	
	n = 241333;
	printf("%d\n", trial_division_sqrt(n));
	printf("%d\n", trial_division_squaring(n));
	printf("%d\n", trial_division_odd(n));
	printf("%d\n", trial_division_primes(n));

	printf("------\n");
	
	n = 2144892013;
	printf("%d\n", trial_division_sqrt(n));
	printf("%d\n", trial_division_squaring(n));
	printf("%d\n", trial_division_odd(n));
	printf("%d\n", trial_division_primes(n));
	
    return 0;
}

