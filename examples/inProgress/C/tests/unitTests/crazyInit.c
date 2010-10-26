#include <stdio.h>
int main(void){
	struct S1 { int arr[3]; } s1 = {1, 2, 3};
	struct S2 { struct S1 s; } s2 = {s1};
	for (int i = 0; i < 3; i++){
		printf("%d\n", s2.s.arr[i]);
	}
	return 0;
}
