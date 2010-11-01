// comb3.c
// part 3/4 of a program expected to be combined

static double global_com2 = 1.0;
extern int foo_com1(int x);

int foo_com3(int x)
{
  return foo_com1(x) + sizeof(int*);
}
  
