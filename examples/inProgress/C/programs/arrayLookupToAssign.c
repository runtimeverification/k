#include <stdio.h>
int main(void){
	int a[5];
	a[0] = 0;
	a[a[0]] = 3;
	printf("%d\n", a[0]);
	return 0;
}
