#include "testharness.h"

int g;
void testg(int x, int err) {
  if(g != 6) E(err);
}

int main()
{
  int x = 7;

  /*
   * Strictly speaking, the order of increment versus assignment here
   * is not well defined: see ANSI C standard section 6.5.2.4 [Postfix
   * increment and decrement operators], paragraph 2.  However, both
   * GCC and VC do the assignment before the side effect.  For maximum
   * compatibility, then, the ending value of x should be 8, not 7.
   */
  x = x++;
  if (x != 8) E(1);


  // Both postincrements happen after the assignment !
  // x == 8
  x = x++ + x++;
  if(x != 18) E(2);

  // The postincrement happens BEFORE the function call !
  g = 5;
  testg(g ++, 5);

  SUCCESS;
}
