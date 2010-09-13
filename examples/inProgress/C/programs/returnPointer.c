#include <stdio.h>
int* f(int*);
int** g(int**);

int main(void){
	int x = 5;
	int* p = f(&x);
	int** q = g(&p);
	if (p != &x){ printf("BUG: different addresses for p and &x\n"); }
	if (q != &p){ printf("BUG: different addresses for q and &p\n"); }
	return x;
}

int* f(int* x){
	(*x)++;
	return x;
}


int** g(int** x){
	(**x)++;
	return x;
}
