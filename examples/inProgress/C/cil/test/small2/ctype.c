// test ctype functions

#include <ctype.h>    // various
#include <stdio.h>    // printf

void analyze(int ch)
{
  printf("character: %c\n", ch);
  printf("  decimal: %d\n", ch);
  printf("  isalpha: %d\n", !!isalpha(ch));
  printf("  isdigit: %d\n", !!isdigit(ch));
}

int main()
{
  analyze('a');
  analyze('5');
  analyze('$');
  analyze('Z');
  return 0;
}

