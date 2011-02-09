#include <stdio.h>
enum hue { chartreuse, burgundy, claret=20, winedark };
int main(void){
	enum hue col, *cp;
	col = claret;
	cp = &col;
	printf("%d ", chartreuse);
	printf("%d ", burgundy);
	printf("%d ", claret);
	printf("%d\n", winedark);
	printf("%d", *cp);
	return 0;
}
