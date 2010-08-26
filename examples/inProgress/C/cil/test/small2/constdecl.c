// tricky const decl

#include <string.h>    // strlen

// first declare the fn
static int foo(char const *a, char const *b);

// now define it using old-style args
static int foo(a, b)
  #if 0
    char const *a, *b;   // looks like we're not associating 'const' with 'b'?
  #else
    char const *a;       // actually, this fails too..
    char const *b;
  #endif
{
  return strlen(a) + strlen(b);
}

int main()
{
  return foo("aa", "bbb") - 5;
}
