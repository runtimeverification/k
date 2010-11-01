#include <stdio.h>
int main(void){
	for (int i = 0; i < 10; i++){
		int arr[++i];
		for (int j = 0; j < i; j++){
			arr[j] = j;
			printf("%d",arr[j]);
		}
		printf("\n");
	}
	return 0;
}
