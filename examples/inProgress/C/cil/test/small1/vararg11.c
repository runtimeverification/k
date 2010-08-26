
/* A test to see if we can split the last argument in a vararg function */
#include <stdarg.h>

// Takes just ints
#pragma ccuredvararg("myvararg", sizeof(int));


int myvararg(char *format, ...) {
  // Make sure the format is a FSEQ
  va_list ap;
  int sum = 0;
  
  va_start(ap, format);
  // Get as many ints as there are letters in the string
  while(*format ++) {
    sum += va_arg(ap, int);
  }
  va_end(ap);

  return sum;
}


int main() {
  if(10 != myvararg("1234", 1, 2, 3, 4))
    return 1;

  return 0;
  
}
