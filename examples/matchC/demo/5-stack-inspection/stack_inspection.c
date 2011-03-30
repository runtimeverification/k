#include <stdio.h>


void trusted(int n);
void untrusted(int n);
void any(int n);


void trusted(int n)
/*@ cfg <stack> S </stack> <out> ?Out </out>
    req n >= 10 \/ inStack(trusted, S) \/ inStack(main, S) */
{
  printf("%d ", n);
  untrusted(n);
  any(n);
  if (n)
    trusted(n - 1);
}

void untrusted(int n)
/*@ cfg <stack> S </stack> <out> ?Out </out>
    req inStack(trusted, S) */
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
//@ var Out : Seq

