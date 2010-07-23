#include <stdio.h>
#include <string.h>
int main(int argc, char* argv[]){
	char a[3] = "abc";
	char b[4];
	memcpy(b, a, 3);
	b[3] = 0;
	printf("%s\n", b);
	printf("%d arguments\n", argc);
	for (int i = 0; i < argc; i++){
		printf("VOLATILE arg%d=%s\n", i, argv[i]);
	}
	if (argv[argc] != NULL){
		printf("ERROR: argv[argc]!=NULL\n");
	}
	return 0;
}
