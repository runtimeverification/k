// examples from http://en.literateprograms.org/Fibonacci_numbers_(C)

unsigned int fib(unsigned int n);
unsigned int fastfib(unsigned int n);
unsigned int fastfib_v2(unsigned int n);
// 0 1 2 3 4 5 6  7  8  9 10
// 0 1 1 2 3 5 8 13 21 34 55
int main(void){
	int x = 0;
	x += fib(10);
	x += fastfib(10);
	x += fastfib_v2(10);
	return x;
}

unsigned int fib(unsigned int n) {
	return n < 2 ? n : fib(n-1) + fib(n-2);
}

unsigned int fastfib(unsigned int n) {
	unsigned int a[3];
	unsigned int *p=a;
	unsigned int i;

	for(i=0; i<=n; ++i) {
		if(i<2) *p=i;
		else {
			if(p==a) *p=*(a+1)+*(a+2);
			else if(p==a+1) *p=*a+*(a+2);
			else *p=*a+*(a+1);
		}
		if(++p>a+2) p=a;
	}

	return p==a?*(p+2):*(p-1);
}

unsigned int fastfib_v2 (unsigned int n) {
  unsigned int n0 = 0;
  unsigned int n1 = 1;
  unsigned int naux;
  unsigned int i;
  if (n == 0)
    return 0;
  for (i=0; i < n-1; i++) {
    naux = n1;
    n1 = n0 + n1;
    n0 = naux;
  }
  return n1;
}


