#include <stdio.h>

extern int myprintf(const char *format, ...);
extern inline int myprintf (const char *format, ...)
{
  int r = printf ("myprintf: ");
  if (r < 0)
    return r;
  int s = printf (format, __builtin_va_arg_pack ());
  if (s < 0)
    return s;
  return r + s;
}
