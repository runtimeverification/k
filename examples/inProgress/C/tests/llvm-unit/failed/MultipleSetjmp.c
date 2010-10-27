#include <setjmp.h>
#include <stdio.h>

int bar(jmp_buf buf, int i)
{
  printf("Inside bar %d\n", i);
  longjmp(buf, i);
}

int main()
{
  jmp_buf buf;
  int ret;

  if ((ret = setjmp(buf)) != 0) {
    printf("returning from bar == %d\n", ret);

    if ((ret = setjmp(buf)) != 0) {
      printf("returning from bar == %d\n", ret);
    } else {
      bar(buf, 927);
    }
  } else {
    bar(buf, 37);
  }
}
