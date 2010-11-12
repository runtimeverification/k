
/*@ logic int pow(int x, int n) */

//@ type int3

/*@ logic int3 prod3(int x1, int x2, int x3) */

/*@ predicate reachable_(int base, int c2, int c1, int c0) */

/*@ ensures \result == 3 * pow(2, 3 * pow(2, pow(3, 3)) + pow(3, 3)) - 1 */
int main(void) 
{
  int c2 = 2;
  int c1 = 2;
  int c0 = 2;
  int base;
  /*@ invariant 0 <= c0 && 0 <= c1 && 0 <= c2 && 0 <= base &&
      reachable_(base,c2,c1,c0)
      variant prod3(c2,c1,c0) for lex3 */
  for(base = 3; 1 ; base++)
    {
      if (0 < c0)
	c0--;
      else if (0 < c1)
	{
	  c1--;
	  c0 = base;
	}
      else if (0 < c2)
	{
	  c2--;
	  c0 = c1 = base;
	}
      else break;
    }
  return base;
}
