
/* Quicksort (no permutation property) */

/*@ requires \valid_index(t,i) && \valid_index(t,j)
  @ assigns t[i],t[j]
  @ ensures t[i] == \old(t[j]) && t[j] == \old(t[i])
  @*/
void swap(int t[],int i,int j);

/*@ predicate sorted(int t[], int i, int j) {
  @   \forall int k; i <= k < j => t[k] <= t[k+1]
  @ }
  @*/

/*@ requires 0 <= l && (l <= r => \valid_range(t,l,r))
  @ assigns  t[l..r]
  @ ensures  sorted(t,l,r)
  @*/
void quick_rec(int t[], int l, int r) {
  if (l < r) {
    int v = t[l];
    int m = l;
    int i = l + 1;
  L:/*@ invariant 
      @   (\forall int j; l < j <= m => t[j] < v) &&
      @   (\forall int j; m < j <  i => t[j] >= v) &&
      @   t[l] == v && l <= m < i <= r + 1
      @ loop_assigns
      @   t[l..r]
      @ variant 
      @   1 + r - i
      @*/
    while (i <= r) {
      if (t[i] < v) { m++; swap(t, i, m); }
      i++;
    }
    swap(t, l, m);
    quick_rec(t, l, m - 1);
    quick_rec(t, m + 1, r);
  }
}

/* At last, the main program, which is just a call to quick_rec */

/*@ requires n >= 1 && \valid_range(t,0,n-1) 
  @ ensures  sorted(t,0,n-1)
  @*/
void quicksort(int t[], int n) {
  quick_rec(t, 0, n-1);
}
