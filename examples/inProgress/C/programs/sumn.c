#include <stdio.h>
#include <stdlib.h>

int sum(int n);

int main(int argc, char* argv[]) {
	//if (argc != 2){ printf("Usage: %s <N>\n", argv[0]); return 1;}
	int input = atoi(argv[1]);
	int result = sum(input);
	printf("sum(%d)==%d\n", input, result);
	return result;
}

int sum(int n) {
	int sum = 0;
	int i = 1;
	while (i <= n){
		sum += i;
		i++;
	}
	return sum;
}
