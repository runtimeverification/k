// arrayinit.c
// char array with initializer exactly filling it, not including NUL
// from sac at stevechamberlain dot com

#include <assert.h>     // assert

char a[5]="12345";      // CIL prior to 8/01/03 16:17 yielded a warning
char b[5]="1234";       // 5th char is a NUL
char c[]="12345";       // 6th char is a NUL
char d[5]="123";        // 4th, 5th char are NULs
//char e[5]="123456";     // too big!  (yields a warning)

int main()
{
  assert(sizeof(a) / sizeof(a[0]) == 5);
  return 0;
}
