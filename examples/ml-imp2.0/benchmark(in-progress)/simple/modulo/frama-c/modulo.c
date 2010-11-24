/*@ requires 
  @   x >= 0 && y > 0
  @ ensures 
  @   0 <= \result < y &&
  @   \exists int d; x == d * y + \result
  @*/
int math_mod(int x, int y) { 
  /*@ invariant 0 <= x && \exists int d; \old(x) == d * y + x
    @ variant x
    @*/
  while (x >= y) x -= y;
  return x;
}
