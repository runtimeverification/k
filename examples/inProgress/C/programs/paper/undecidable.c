#include <stdio.h>
// assumes sizeof(int) == sizeof(int*)
int main(void) {
	int** mem[2];
	int*** p = &mem[0];
	mem[0] = (int**)p;
	mem[1] = (int**)5;
	printf("&mem[0]==%p\n\n", p);
	printf("mem[0]==%p\n", mem[0]);
	printf("mem[1]==%p\n", mem[1]);
	printf("...\n");
	int* result = (*((*p)++))++;
	printf("mem[0]==%p\n", mem[0]);
	printf("mem[1]==%p\n", mem[1]);
	printf("\nresult==%p\n", (int*)result);
	//return result - &mem[0];
	return 0;
}
