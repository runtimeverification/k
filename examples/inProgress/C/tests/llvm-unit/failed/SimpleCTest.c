#include <setjmp.h>

void baz(jmp_buf buf)
{
  printf("Inside baz\n");
  longjmp(buf, 37);
}

int main()
{
  jmp_buf buf;
  int ret;

  printf("Inside main\n");

  if ((ret = setjmp(buf)) != 0) {
    printf("ret == %d\n", ret);
  } else {
    baz(buf);
  }

  return 0;
}
