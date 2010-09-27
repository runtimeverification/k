#include <stdlib.h>
int* f(int x[]);

typedef struct str {
	int (*funcArr[2])(void);
	int (*funcArr2D[2][2])(void);
} strdef ;

typedef struct that {
	struct str this;
} thatdef ;

thatdef globalThat;

int main(void){
	thatdef t;
	t.this.funcArr[0] = main;
	globalThat.this = t.this;
	return 0;
}
