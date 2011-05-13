#include <stdio.h>

int main() {
	int n;
	int sum;
	int i;
	sum = 0;
	i = 0;
	scanf("%d", &n);
	while (n > i) {
		sum = sum + i;
		i++;
	}
	printf("%d;", sum);
}
