#include <stdio.h>

struct globalStruct {
	int a;
} aGlobalStruct;

enum e_tag{
      a, b, c, d=20, e, f, g=20, h_h
}var;

typedef enum e_tag myenum;

int main(void){
	if (a != 0){ printf("a==%d", a); }
	if (b != 1){ printf("b==%d", b); }
	if (c != 2){ printf("c==%d", c); }
	if (d != 20){ printf("d==%d", d); }
	if (e != 21){ printf("e==%d", e); }
	if (f != 22){ printf("f==%d", f); }
	if (g != 20){ printf("g==%d", g); }
	if (h_h != 21){ printf("h_h==%d", h_h); }

	enum e_tag col, *cp;
	col = d;
	cp = &col;
	if (*cp != d){
		printf("*cp==%d\n", *cp);
	}
	int eint = col;
	char echar = col;
	long long int elli = col;
	col = (char)d;
	col = (int)d;
	col = (long long int)d;
	
	myenum foo = d;
	myenum bar = g;
	if (d != g){
		printf("d==%d, g==%d\n", d, g);
	}
	
	var = h_h;
	if (var != 21){
		printf("var==%d\n", var);
	}
	
	aGlobalStruct.a = a;
	if (aGlobalStruct.a != a){
		printf("aGlobalStruct.a==%d\n", aGlobalStruct.a);
	}
	
	return 0;
}
