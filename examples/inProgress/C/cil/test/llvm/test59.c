#include <stdio.h>
#include <stdarg.h>

typedef __builtin_va_list __gnuc_va_list;

extern int vfprintf (FILE *__restrict __s, __const char *__restrict __format,
		     __gnuc_va_list __arg);

int wprintf (__const char *__restrict __fmt, __gnuc_va_list __arg)
{
  return vfprintf (stdout, __fmt, __arg);
}

void xprintf(__const char *__restrict __fmt, ...)
{
  va_list vl;

  va_start(vl, __fmt);
  wprintf(__fmt, vl);
  va_end(vl);
}

int main()
{
  xprintf("foo\n");
  return 0;
}
