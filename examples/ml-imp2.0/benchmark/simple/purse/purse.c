#include <stdlib.h>
#include <stdio.h>

struct purse {
  int balance;
} ;

struct purse* credit(struct purse *p, int s)
{
  p->balance = p->balance + s;
  return p;
}

struct purse* withdraw(struct purse *p, int s)
{
  p->balance = p->balance - s;
  return p;
}

int main()
{
  struct purse* p1;
  struct purse* p2;
  int s;
  p1 = (struct purse*)malloc(sizeof(struct purse));
  p2 = (struct purse*)malloc(sizeof(struct purse));
  printf("%d %d\n",p1->balance,p2->balance);
  p1->balance = 0;
  printf("%d %d\n",p1->balance,p2->balance);
  p2->balance = 320;
  s = 100;

  credit(p2,s);
  printf("%d %d\n",p1->balance,p2->balance);
  return 0;
}

