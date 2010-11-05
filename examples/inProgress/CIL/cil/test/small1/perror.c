void perror_1();

#include <stdio.h>

void perror_1 (string) 
char * string;
{
  char *copy = "hello";
  perror (copy);
}

int main(int argc, char ** argv) {
  return 0;
}




