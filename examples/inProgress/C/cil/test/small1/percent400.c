#include <stdio.h>

int main (void) {
  char buf[10] = "abc", *str;
  sscanf(buf, "%400", str);
  return 0;
}
