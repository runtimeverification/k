// bzero.c
// we call bzero w/o any complaint?

//#include <strings.h>     // bzero

char buf[80];

int main()
{
  bzero(buf, (void*)80);     // this is how anagram does it
  return 0;
}
