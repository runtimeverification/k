#include <stdio.h>
int main(void){
	const char* a = "a";
	const char* b = "b";
	const char* c = "c";
	return printf(a) + (printf(b) + printf(c));
}
