/* Sourceforge bug #2201218, #1852730 */
int a, b, c;
int *chrdevs[] = { &a, &b, &c };

struct { int z; } zz;

void f(void)
{
  int i;

  for (i = (sizeof(chrdevs) / sizeof((chrdevs)[0]) +
	    (sizeof(char[1 - 2 * !!(__builtin_types_compatible_p(typeof(chrdevs), typeof(&chrdevs[0])))]) - 1))-1; i > 0; i--) 
    {
      if (chrdevs[i] == ((void *)0))
	break;
    }
}
