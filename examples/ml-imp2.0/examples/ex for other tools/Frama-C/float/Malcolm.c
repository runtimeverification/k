/*@ logic int my_log(real s) */

/*@ ensures \result == 2 ^^ (53) */

double malcolm1() {
  double A;
  A=2;
  /*@ assert A==2 */

  /*@ invariant A== 2 ^^ my_log(A) && 
              1 <= my_log(A) <= 53
      variant (53-my_log(A)) */

  while (A != (A+1)) {
    A*=2;
  }
  return A;

}
