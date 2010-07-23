#include <stdio.h>

struct _s {int a[5]; int x; int y;};
int main() {
	struct _s s = {{1, 2, 3, 4, 5}, 6, 0};
	int i = 0;
	while (s.a[i] != 0){
		printf("s.a[%d]==%d\n", i, s.a[i]);
		i++;
	}
}
