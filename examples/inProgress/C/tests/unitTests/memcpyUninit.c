#include <stdio.h>
#include <stdlib.h>
#include <string.h>
struct S {
	int x;
	int y;
};
int main(void){
	struct S s1;
	s1.x = 5;
	struct S *s2 = malloc(sizeof(struct S)) ;
	memcpy(s2, &s1, sizeof(struct S));
	
	printf("%d\n", s2->x);
	return 0;
}
