#include <stdio.h>

//int f(unsigned long long int);
int f(unsigned long long int);

int main(void){
	char* mychar[] = {"file"};
	char x = 5;
	f(x);
	return 0;
}

int f(unsigned long long int x){
	printf("ull %d\n", x);
	return 0;
}
