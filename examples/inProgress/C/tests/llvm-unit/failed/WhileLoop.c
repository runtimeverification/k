#include <setjmp.h>
#include <stdio.h>

void foo(jmp_buf buf, int i)
{
  printf("Inside foo: %d\n", i);
  longjmp(buf, i);
}

int main()
{
  int i = 37;

  while (i--) {
    jmp_buf buf;
    int ret;

    if ((ret = setjmp(buf)) != 0) {
      printf("Return from longjmp: %d\n", ret);
    } else {
      foo(buf, i);
    }
  }
}
