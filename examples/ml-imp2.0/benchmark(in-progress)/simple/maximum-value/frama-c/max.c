/*@ ensures 
  @   \result >= x && \result >= y &&
  @   \forall int z; z >= x && z >= y => z >= \result 
  @*/
int max(int x, int y) {
  if (x > y) return x; else return y;
}
