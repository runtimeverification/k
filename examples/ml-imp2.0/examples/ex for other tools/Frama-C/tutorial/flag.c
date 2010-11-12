
/* Dijkstra's dutch flag */

typedef enum { BLUE, WHITE, RED } color;

//@ predicate isColor(int i) { i == BLUE || i == WHITE || i == RED }

/*@ predicate isMonochrome(int t[], int i, int j, color c)
  @   { \valid_range(t,i,j) && \forall int k; i <= k && k <= j => t[k] == c } 
  @*/

/*@ requires \valid_index(t,i) && \valid_index(t,j)
  @ assigns t[i],t[j]
  @ ensures t[i] == \old(t[j]) && t[j] == \old(t[i])
  @*/
void swap(int t[], int i, int j);

/*@ requires n >= 0 &&
  @   \valid_range(t,0,n-1) &&
  @   (\forall int k; 0 <= k && k < n => isColor(t[k]))
  @ assigns t[0 .. n-1]
  @ ensures 
  @   (\exists int b, int r; 
  @            isMonochrome(t,0,b-1,BLUE) &&
  @            isMonochrome(t,b,r-1,WHITE) &&
  @            isMonochrome(t,r,n-1,RED))
  @*/
void flag(int t[], int n) {
  int b = 0;
  int i = 0;
  int r = n;
  /*@ invariant 
    @   (\forall int k; 0 <= k && k < n => isColor(t[k])) &&
    @   0 <= b && b <= i && i <= r && r <= n &&
    @   isMonochrome(t,0,b-1,BLUE) &&
    @   isMonochrome(t,b,i-1,WHITE) &&
    @   isMonochrome(t,r,n-1,RED)
    @ variant r - i
    @*/
  while (i < r) {
    switch (t[i]) {
    case BLUE:  
      swap(t, b++, i++);
      break;	    
    case WHITE: 
      i++; 
      break;
    case RED: 
      swap(t, --r, i);
      break;
    }
  }
}

