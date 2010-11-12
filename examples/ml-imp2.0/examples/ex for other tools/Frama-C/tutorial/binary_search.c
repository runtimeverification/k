
/*@ axiom mean_1 : \forall int x, int y; x <= y => x <= (x+y)/2 <= y */

/*@ requires 
  @   n >= 0 && \valid_range(t,0,n-1) &&
  @   \forall int k1, int k2; 0 <= k1 <= k2 <= n-1 => t[k1] <= t[k2]
  @ ensures
  @   (\result >= 0 && t[\result] == v) ||
  @   (\result == -1 && \forall int k; 0 <= k < n => t[k] != v)
  @*/
int binary_search(int* t, int n, int v) {
  int l = 0, u = n-1, p = -1;
  /*@ invariant 
    @   0 <= l && u <= n-1 && -1 <= p <= n-1
    @   && (p == -1 => \forall int k; 0 <= k < n => t[k] == v => l <= k <= u)
    @   && (p >= 0 => t[p]==v)
    @ variant u-l 
    @*/
  while (l <= u ) {
    int m = (l + u) / 2;
    //@ assert l <= m <= u
    if (t[m] < v)
      l = m + 1;
    else if (t[m] > v)
      u = m - 1;
    else {
      p = m; break;
    }
  }
  return p;
}
