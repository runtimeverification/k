#include "testharness.h"
#include <string.h>
char a[10];

__inline static char * __wes_memset_generic(char *s, char c, unsigned int count)
{
    int d0;
    int d1;

    __asm__ __volatile__("rep\n\t"
    			 "stosb": "=&c" (d0), "=&D" (d1): "a" (c), "1" (s),
			 "0" (count): "memory");
    return s;
}

int main() {
    char *res;
    int i;
    for (i=8;i>0;i--)
    	a[i] = '!';	// force SEQ pointer
    res = __wes_memset_generic(a, 'g', 1); 
    res = __wes_memset_generic(a+1, 'o', 2); 
    res = __wes_memset_generic(a+3, 'd', 1); 
    if (strncmp(a,"good!!!!!",10)) {
	E(1);
    }
    SUCCESS;
}






