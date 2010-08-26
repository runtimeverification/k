/*
   chunk2.c - show that the CIL merger fails to rename a symbol when it must.

   In this file, we declare chunk to be a static variable.
   In another file we declare it to be a typedef.
   One of these two must get renamed but neither is.

   Test on Cygwin under Windows XP using CIL 1.2.4.

   See chunk1.c comments for step-by-step reproduction of bug.
*/

extern int chunk1(char*);

static char fake[1] ;
static char *chunk = fake;

int main(void)
{
  return chunk1(chunk) - fake[0];
}

  
