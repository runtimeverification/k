#include <stdio.h>
int main(void){
	int i = 0;
	while(i < 10){
		i++;
		printf("%d\n", i);
		{ int i; i = 10; continue;}
		printf("passed continue\n");
	}
	printf("done\n");
	return 0;
}
