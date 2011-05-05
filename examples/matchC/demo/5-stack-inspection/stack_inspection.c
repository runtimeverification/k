#include <stdio.h>


void trusted(int n);
void untrusted(int n);
void any(int n);


void trusted(int n)
/*@ rule <k> $ => return; </k> <stack> S </stack> <out_> epsilon => A </out>
    if n >= 10 \/ in(hd(ids(S)), {main, trusted}) */
{
  printf("%d ", n);
  //untrusted(n);
  any(n);
  if (n)
    trusted(n - 1);
}

void untrusted(int n)
/*@ rule <k> $ => return; </k> <stack> S </stack> <out_> epsilon => A </out>
    if find(trusted, ids(S)) /\ n = n */
{
  printf("%d ", -n);
  if (n)
    any(n - 1);
}

void any(int n)
{
  // untrusted(n);
  if(n > 10)
    // possible security violated if n < 10
    trusted(n - 1);  
}


int main()
{
  trusted(5);
  any(5);

  return 0;
}


//@ var S : ListItem
//@ var A : Seq

