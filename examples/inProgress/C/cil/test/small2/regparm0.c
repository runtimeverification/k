// regparm0.c
// test of the regparm(0) problem in linux/arch/i386/kernel/signal.c

// first, problematic prototype; basically, the regparm(0) is
// parsed as associated with the return type (int), and hence a
// no-op; the regparm(3) should be what's attached to do_signal
__attribute__((regparm(0)))  int  do_signal(int *regs, int *oldset)
   __attribute__((regparm(2))) __attribute__((regparm(3)));

// call this function
int main()
{
  int r=6, o=5;
  return do_signal(&o, &r) - 11;
}

// now an implementation which will die if its args are mis-passed
int do_signal(int *regs, int *oldset)
{
  return *regs + *oldset;
}




