#include <stdio.h>

typedef struct {
  char name [80];
  int val;
  unsigned uval;
} data;

static int callback(void *d);
static void iter(int (*)(void*), void *);

static int callback(void *d)
{
  data *iter_data = (data *)d;

  printf("%u\n", iter_data->uval);
  return iter_data->uval == 0;
}

static void iter(int (*cb)(void*), void *d)
{
  cb(d);
}

int main()
{
  data d;

  d.uval = 0;
  iter(callback, &d);
  return 0;
}
