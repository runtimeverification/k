#include <stdarg.h>
#include <stdio.h>
f (int n, ...) {
	va_list args;

	va_start (args, n);
	printf("%d\n", va_arg (args, int));

	if (va_arg (args, long long) != 10000000000LL)
		abort ();
	
	printf("%d\n", va_arg (args, int));

	if (va_arg (args, long double) != 3.14L)
		abort ();
	
	printf("%d\n", va_arg (args, int));
	printf("%d\n", va_arg (args, int));

	if (va_arg (args, long long) != 20000000000LL)
		abort ();
	
	printf("%d\n", va_arg (args, int));

	if (va_arg (args, double) != 2.72)
		abort ();

	va_end(args);
}

main ()
{
  f (4, 10, 10000000000LL, 11, 3.14L, 12, 13, 20000000000LL, 14, 2.72);
  exit (0);
}
