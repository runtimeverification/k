// comparison of 0 and '\0' ..

#include <stdio.h>     // printf

int main()
{
  int *i = (int*)512;         // low byte is 0
  char c = (char)i;           // should be 0

  printf("i: %d\n", (int)i);
  printf("c: %d\n", (int)c);

  if (i == '\0') {
    printf("yes. This is not correct!!\n");          // cil'd code does this!
    return 1;
  }
  else {
    printf("no\n");           // ordinary gcc does this
  }

  if ((int)(char)i == (int)'\0') {
    printf("2nd yes\n");      // ordinary gcc does this
  }
  else {
    printf("2nd no\n");
  }
  printf("Success\n");
  return 0;
}
