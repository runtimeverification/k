#include <stdio.h>

int fold(int* arr, int length, int start, int (*)(int, int));
int sum(int x, int y);

int main(void){
	int arr[] = {1, 2, 3, 4, 5};
	
	int res = fold(arr, sizeof(arr)/sizeof(arr[0]), 0, sum);
	printf("%d", res);
	return 0;
}

int fold(int* arr, int length, int start, int (*f)(int, int)){
	int res = start;
	for (int i = 0; i < length; i++){
		res = (*f)(res, *(arr + i));
	}
	return res;
}

int sum(int x, int y){
	return x + y;
}