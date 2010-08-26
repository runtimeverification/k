// test simple character functions, which give us
// troubles because they are macros

#include <stdio.h>      // putc
#include <unistd.h>     // unlink

int main()
{
  FILE *tmp;
  int ch;

  putc('c', stdout);
  putc('\n', stdout);

  tmp = fopen("putc.tmp", "w");
  fputc('a', tmp);
  fclose(tmp);

  tmp = fopen("putc.tmp", "r");
  ch = fgetc(tmp);
  fclose(tmp);
  if (ch != 'a') {
    return 4;
  }

  unlink("putc.tmp");
  
  puts("putc seems to work");   // puts outputs a trailing newline
  
  return 0;
}
