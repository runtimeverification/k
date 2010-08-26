/* A example program that reads from stdin and writes to stdout */
// based on http://en.wikibooks.org/wiki/C_Programming/File_IO
#include <stdio.h>
#include <stdlib.h>

#define BUFFER_SIZE 100

int main(void) {
	FILE * fp = fopen("trial.txt", "r");
	int myChar;
	while((myChar = fgetc (fp)) != EOF) {
		//putc(myChar, stdout);
		putchar(myChar);
	}
	fclose(fp);
	fp = fopen("trial.txt", "r");
	char buffer[BUFFER_SIZE]; /* a read buffer */
	while(fgets (buffer, (BUFFER_SIZE-1), fp)) {
		printf(buffer);
	}
	
	return 0;
}
/* end program. */
