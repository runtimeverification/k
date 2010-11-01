#undef assert
#if defined NDEBUG
#define assert(test) (void)0
#else
#include <stdio.h>
#include <stdlib.h>
#define assert(test) if (!(test)) {printf("Assertion failed: `%s', file %s, line %u\n", #test, (__FILE__), (__LINE__)); abort();} (void)0
#endif
