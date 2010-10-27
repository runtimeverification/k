/*
 * This tests that longjmp can jump from a function far down in the
 * calling chain and past other, non-accepting setjmps.
 */
#include <setjmp.h>
#include <stdio.h>

void quux(jmp_buf buf)
{
  printf("Inside quux\n");
  printf("Longjmping from quux: 927\n");
  longjmp(buf, 927);
}

void qux(jmp_buf buf)
{
  jmp_buf local_buf;

  printf("Inside qux\n");

  if (!setjmp(local_buf))
    quux(buf);
  else
    printf("Error: Shouldn't be here in qux\n");
}

void baz(jmp_buf buf)
{
  jmp_buf local_buf;

  printf("Inside baz\n");

  if (!setjmp(local_buf))
    qux(buf);
  else
    printf("Error: Shouldn't be here in baz\n");
}

void bar(jmp_buf buf)
{
  printf("Inside bar\n");
  baz(buf);
}

void foo()
{
  jmp_buf buf;

  printf("Inside foo\n");

  if (!setjmp(buf))
    bar(buf);
  else
    printf("Returning from longjmp into foo\n");
}

int main()
{
  foo();
  return 0;
}
