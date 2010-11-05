#include <stdio.h>
int main(void){
#if __GNUC__
	puts("VOLATILE: uses __gnuc__");	
#else 
	puts("VOLATILE: no __gnuc__");
#endif
	return 0;
}
