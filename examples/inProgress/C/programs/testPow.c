#include <math.h>
#include <stdio.h>

int main(void){
	for (int i = 0; i < 10; i++) {
		for (int j = 0; j < 10; j++) {
			printf("%d ^ %d == %d\n", i, j, (int)pow(i, j));
			//printf("%f ^ %f == %f\n", (double)i, (double)j, pow(i, j));
		}
	}
	return 0;
}
