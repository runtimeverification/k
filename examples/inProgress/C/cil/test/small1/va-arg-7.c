void exit(int);
void abort(void);

// From c-torture
/* Origin: Franz Sirl <Franz.Sirl-kernel@lauterbach.com> */
//modified for stdarg.h

#pragma ccuredvararg("debug", sizeof(union { int i; double d;}))

#if __GNUC__ >= 3 || !defined __GNUC__

#include <stdarg.h>
inline void
debug(int i1, int i2, int i3, int i4, int i5, int i6, int i7, 
      double f1, double f2, double f3, double f4, double f5, double f6,
      double f7, double f8, double f9, 
      ...)
#else
//old version:
#include <varargs.h>
inline void
debug(i1, i2, i3, i4, i5, i6, i7, f1, f2, f3, f4, f5, f6, f7, f8, f9, va_alist)
     int i1, i2, i3, i4, i5, i6, i7;
     double f1, f2, f3, f4, f5, f6, f7, f8, f9;
     va_dcl

#endif
{
  va_list ap;

#if __GNUC__ >= 3 || !defined __GNUC__
  va_start (ap, f9);
#else
  va_start (ap); //varargs.h
#endif

  if (va_arg (ap,int) != 8)
    abort ();
  if (va_arg (ap,int) != 9)
    abort ();
  if (va_arg (ap,int) != 10)
    abort ();

  va_end (ap);
}

int
main(void)
{
  debug (1, 2, 3, 4, 5, 6, 7, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0,
         8.0, 9.0, 8, 9, 10);
  exit (0);
}
