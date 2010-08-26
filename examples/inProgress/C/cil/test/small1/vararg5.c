#include "testharness.h"


/* 
This file is a test for variable argument functions, where the call to 
print is made in a separate function, talking. This checks to see if we 
can retrieve the arguments in a variable argument function if we call a 
separate function.
*/

#include <stdarg.h>
#include <stddef.h>
#include <stdio.h>
#include <fcntl.h>
#include <string.h>

#pragma ccuredvararg("talking", printf(2))
void talking(FILE *out, char *s, ...);

int main(int argc, char** argv) {
  int x, y;
  char* s;
  char buff[128];
  float f = 5.0;
  double d = 10.0;
  
  FILE *out = fopen("vararg.out", "w+");
  if(! out) E(1);
  
  x = 5;
  y = 1;
  s = "hello";
  talking(out, "%d %3.1f %3.1f\n", x, f, d);
  fseek(out, 0, SEEK_SET);
  fread(buff, 1, sizeof(buff)-1, out);
  fclose(out);
  buff[10] = '\0';
  printf("Should be 5 5.0 10.0: %s\n", buff);
  if(strncmp(buff, "5 5.0 10.0", 10)) E(2);
  SUCCESS;
}

void talking(FILE *out, char* s, ...) {
  va_list ap;
  va_start(ap, s);
  vfprintf(out, s, ap);
  va_end(ap);
}
