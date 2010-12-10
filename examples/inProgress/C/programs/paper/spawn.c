#include <stdio.h>
void spawn(int (*a)(int), int b, ...);
void sync();

int g(int x, int y){
	printf("(%d, %d)\n", x, y);
	return 0;
}

int f(int x) {
	printf("inside f: %d\n", x);
	g(x, 0);
	//spawn(g, x, 0);
	//spawn(g, x, 1);
	return 0;
}
int main(void){
	spawn(f, 1, 0);
	spawn(f, 1, 1);
	
	sync();
	return 0;
}

/*
4! == 24
< output > String "(0, 0)\n(0, 1)\n(1, 0)\n(1, 1)\n"(.List{K}) </ output > 
< output > String "(0, 0)\n(0, 1)\n(1, 1)\n(1, 0)\n"(.List{K}) </ output > 
< output > String "(0, 0)\n(1, 0)\n(0, 1)\n(1, 1)\n"(.List{K}) </ output > 
< output > String "(0, 0)\n(1, 0)\n(1, 1)\n(0, 1)\n"(.List{K}) </ output > 
< output > String "(0, 0)\n(1, 1)\n(0, 1)\n(1, 0)\n"(.List{K}) </ output > 
< output > String "(0, 0)\n(1, 1)\n(1, 0)\n(0, 1)\n"(.List{K}) </ output > 
< output > String "(0, 1)\n(0, 0)\n(1, 0)\n(1, 1)\n"(.List{K}) </ output > 
< output > String "(0, 1)\n(0, 0)\n(1, 1)\n(1, 0)\n"(.List{K}) </ output > 
< output > String "(0, 1)\n(1, 0)\n(0, 0)\n(1, 1)\n"(.List{K}) </ output > 
< output > String "(0, 1)\n(1, 0)\n(1, 1)\n(0, 0)\n"(.List{K}) </ output > 
< output > String "(0, 1)\n(1, 1)\n(0, 0)\n(1, 0)\n"(.List{K}) </ output > 
< output > String "(0, 1)\n(1, 1)\n(1, 0)\n(0, 0)\n"(.List{K}) </ output > 
< output > String "(1, 0)\n(0, 0)\n(0, 1)\n(1, 1)\n"(.List{K}) </ output > 
< output > String "(1, 0)\n(0, 0)\n(1, 1)\n(0, 1)\n"(.List{K}) </ output > 
< output > String "(1, 0)\n(0, 1)\n(0, 0)\n(1, 1)\n"(.List{K}) </ output > 
< output > String "(1, 0)\n(0, 1)\n(1, 1)\n(0, 0)\n"(.List{K}) </ output > 
< output > String "(1, 0)\n(1, 1)\n(0, 0)\n(0, 1)\n"(.List{K}) </ output > 
< output > String "(1, 0)\n(1, 1)\n(0, 1)\n(0, 0)\n"(.List{K}) </ output > 
< output > String "(1, 1)\n(0, 0)\n(0, 1)\n(1, 0)\n"(.List{K}) </ output > 
< output > String "(1, 1)\n(0, 0)\n(1, 0)\n(0, 1)\n"(.List{K}) </ output > 
< output > String "(1, 1)\n(0, 1)\n(0, 0)\n(1, 0)\n"(.List{K}) </ output > 
< output > String "(1, 1)\n(0, 1)\n(1, 0)\n(0, 0)\n"(.List{K}) </ output > 
< output > String "(1, 1)\n(1, 0)\n(0, 0)\n(0, 1)\n"(.List{K}) </ output > 
< output > String "(1, 1)\n(1, 0)\n(0, 1)\n(0, 0)\n"(.List{K}) </ output > 

*/
