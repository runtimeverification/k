
/*@ predicate is_min(int t[],int n,int min) {
  @	(\forall int i; 0 <= i < n => min <= t[i]) &&
  @	(\exists int i; 0 <= i < n && min == t[i]) 
  @ }
  @*/

/* analogue pour is_max */

/*@ requires n > 0 && \valid_range(t,0,n)
  @ ensures is_min(t,n,\result) 
  @*/
int min(int t[],int n) {
  int i;
  int tmp = t[0];  
  /*@ invariant 1 <= i <= n && is_min(t,i,tmp)
    @ variant n-i
    @*/
  for (i=1 ; i < n; i++) {
     if (t[i] < tmp) tmp = t[i];
  }
  return tmp;
}


/*@ logic int min(int t[],int n) reads t[..] */
/*@ logic int max(int t[],int n) reads t[..] */

/*@ axiom min_is_min:
  @    \forall int t[]; \forall int n; n > 0 => is_min(t,n,min(t,n))
  @*/

/*@ axiom is_min_is_min:
  @    \forall int t[]; \forall int n; n > 0 => \forall int m;
  @         is_min(t,n,m) => m == min(t,n)
  @*/

/*@ requires \valid_range(t,0,n) && n > 0
  @ ensures 
  @     min(t,n) <= \result 
  @*/
int average(int t[],int n) {
  int i;
  int sum = 0;  
  /*@ invariant 0 <= i <= n && i * min(t,i) <= sum
    @ variant n-i
    @*/
  for (i=0 ; i < n; i++) {
     sum += t[i];
  }
  return sum / n;
}
