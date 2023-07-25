#include <stdio.h>

char *parse_KItem(char *, char *);

int main(int argc, char **argv) { printf("%s\n", parse_KItem(argv[1], NULL)); }
