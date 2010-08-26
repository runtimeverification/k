#if defined (HAVE_SOCKETS)
#include <stdio.h>
int main() {
  printf("how did i get here?");
}

#else

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

#endif


