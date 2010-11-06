//#include <stdio.h>
// from http://www.open-std.org/jtc1/sc22/wg14/www/docs/n926.htm
int f(int x){ return 0; }

struct s0 { double p; int q; int r; } *sp, s; 

int main(void) {
    int x,y, z;
	int a[2] = {0, 0};
	int *ap;
	
	// example 2
	// should be undefined
    x = ++x;
	
	// example 3
	// should be defined
	x += x * x;
	
	// example 4
	// should be defined
	x = f(x++); 
	
	// example 5
	// should be undefined
	(x=y) + x;
	
	// example 6
	// should be undefined
	(x=y) + (x=z);
	
	// example 9
	// should be defined
	sp = &s;
    sp->q = sp->r;
	
	// example 11
	// well defined
	x++ && x--;
	
	// example 12
	// well defined
	x++ * y++ ? x-- : y --;

	// example 13
	// undefined
	ap=a;  *ap = f(ap++);
	
	// example T1
	// defined
	*(*p=2, p) = 7;
	
	// 12.1
	// undefined
	(x++ , x) + (x-- , x)
	
	return 0;
}
