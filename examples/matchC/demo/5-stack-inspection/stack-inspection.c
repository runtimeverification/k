#include <stdio.h>

// The trusted function should only be called from the main function or from itself.
// The untrusted function should only be called directly or indirectly by the trusted function.

void untrusted(int);
void any(int);

void trusted(int n)
/* pre <stack> S,trusted(?m) </stack>
   \/ <stack> S,main() </stack> */
{
  printf("%d ", n);
  untrusted(n);
  any(n);
  if (n) trusted(n-1);
}

void untrusted(int n)
// pre <stack> S,trusted(?m),S' </stack>
{
  printf("%d ", -n);
  if (n) any(n-1);
}

void any(int n) {
  untrusted(n);
  //  if(n) trusted(n-1);  // security violated when this line is included
}

int main() {
  trusted(10);
  any(10);             // security violated when this line is included
}
