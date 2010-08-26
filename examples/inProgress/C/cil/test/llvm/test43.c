#include <stdio.h>
#include <stdarg.h>

void myprintf(char *extra, char *fmt, ...)
{
  va_list pargs;

  fputs(extra, stdout); putc(':', stdout);
  va_start(pargs, fmt);
  vprintf(fmt, pargs);
  va_end(pargs);
}

int main(int argc, char **argv)
{
  myprintf("yes", "hello world %d\n", 12);
  return 0;
}
