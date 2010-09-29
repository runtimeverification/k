// adapted from http://www.cis.temple.edu/~ingargio/cis71/code/prime1.c

/* prime1.c  It prompts the user to enter an integer N. It prints out
 *           if it is a prime or not. If not, it prints out a factor of N.
 */

#include <stdio.h>
int prime(int n);

int main(void) {
	return prime(2) + prime(7) + prime(8) + prime(31); // should be 3
}

int prime(int n){
  int i;
  int flag;

  flag = 1;
  for (i=2; (i<(n/2)) && flag; ) { /* May be we do not need to test
			values of i greater than the square root of n? */
    if ((n % i) == 0) /* If true n is divisible by i */
      flag = 0;
    else
      i++;
  }
 
	if (flag)
		return 1;
	else
		return 0;
}
