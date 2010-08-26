#include "testharness.h"
extern int strlen(const char *);
/* GCC allows a bunch of escapes in strings */


char *str = "\( \{ \[ \% \x20 \e \E \a \b \f \n \r \t \v \? \\ \' ";

int main() {
  if(strlen(str) != 34) E(1);
  return 0;
}
