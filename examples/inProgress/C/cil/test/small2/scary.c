// scary.c
// seeing what gcc is afraid of

#include <stdio.h>     // printf
#include <stdlib.h>    // atoi
#include <sys/time.h>  // struct timeval, gettimeofday

// return the # of milliseconds since some unspecified, but
// constant for the life of the program, event
long getMilliseconds()
{
# ifdef __WIN32__
    // # of milliseconds since program started
    return GetTickCount();

# else
    // some unspecified millisecond count (unspecified
    // because tv.tv_sec * 1000 will overflow a 32-bit
    // long, for typical values)
    struct timeval tv;
    gettimeofday(&tv, NULL);
      // according to HPUX man page, this always returns 0 and does
      // not have any errors defined

    //printf("tv.tv_sec = %d, tv.tv_usec = %d\n",
    //       tv.tv_sec, tv.tv_usec);
    return tv.tv_sec * 1000 + tv.tv_usec / 1000;
# endif
}

int loop1(int m)
{
  int i=0;
  while (i<m) {
    i++;
  }
  return i;
}

int loop2(int m)
{
  int i=0;
  while (i<m) {
    (*&i)++;
  }
  return i;
}

int loop3(int m)
{
  int i=0;
  while (*&i < m) {
    i++;
  }
  return i;
}

int loop4(int m)
{
  int i=0;
  while (*&i < m) {
    (*&i)++;
  }
  return i;
}


int main(int argc, char *argv[])
{ 
  int m;           
  long start;

  if (argc < 2) {
    printf("usage: %s <iters>\n", argv[0]);
    return 0;
  }

  m = atoi(argv[1]);

  #define LOOP(n)                                  \
    start = getMilliseconds();                     \
    printf("loop%d: ", n);                         \
    loop##n(m);                                    \
    printf("%ld ms\n", getMilliseconds() - start) /* user ; */

  LOOP(1);
  LOOP(2);
  LOOP(3);
  LOOP(4);

  printf("done\n");

  return 0;
}


