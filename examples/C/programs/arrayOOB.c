#include <stdio.h>
#include <string.h>

int main(void){
	//char dest[5], src[5] = "hello";
	char dest[6], src[6] = "hello";
	strcpy(dest, src);
	printf("%s\n", dest);
	return 0;
}
