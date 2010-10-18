#include <stdio.h>
#include <stdlib.h>

int main() {
	int count = 101;
	int* src = (int*)malloc(count * sizeof(int));
	int* dest = (int*)malloc(count * sizeof(int));
	int* origSrc = src;
	int* origDest = dest;
	for (int i = 0; i < count; i++){
		src[i] = i * 2 + 1;
		dest[i] = 0;
	}

	int n = (count+7)/8;
	
	switch(count%8) {
		case 0:	do{	*dest++ = *src++;
		case 7:		*dest++ = *src++;
		case 6:		*dest++ = *src++;
		case 5:		*dest++ = *src++;
		case 4:		*dest++ = *src++;
		case 3:		*dest++ = *src++;
		case 2:		*dest++ = *src++;
		case 1:		*dest++ = *src++;
		} while(--n>0);
	}
	
	for (int i = 0; i < count; i++){
		printf("%d: src=%d, dest=%d\n", i, origSrc[i], origDest[i]);
	}
	return 0;
}
