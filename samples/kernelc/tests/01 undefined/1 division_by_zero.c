/*
 * The program below performs a division by zero.  Since MatchC is based
 * on the executable semantics of the language and since no semantics has
 * been given for division-by-zero, the program below gets stuck
 * when verified, the same way it gets stuck when executed semantically.
 * Indeed, if you check the error message you can see 3/0 on the top
 * of the computation cell <k> ... </k>.
 */


#include <stdio.h>


int main()
{
  int x;
  x = 0;
  printf("%d", 3/x);
}
