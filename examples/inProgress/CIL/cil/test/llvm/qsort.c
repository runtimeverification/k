#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

extern char *optarg;
void seq_sort(int base, int n);

#define DEBUG

int *from, *to;
int size = 8;
void (*selected_sort)(int base, int n) = seq_sort;

void usage(void)
{
  fprintf(stderr, "Usage: qsort -sSEED -nSIZE -[123]\n");
  exit(2);
}

int intopt(int min)
{
  int n = atoi(optarg);

  if (n < min)
    usage();
  return n;

}

void setup(int argc, char **argv)
{
  int opt, i;

  srand48(42);

  while ((opt = getopt(argc, argv, "s:n:1234")) != -1)
    switch (opt)
      {
      case 's': srand48(intopt(1)); break;
      case 'n': size = intopt(2); break;
      case '1': selected_sort = seq_sort; break;
      default: usage();
      }

  from = malloc(size * sizeof *from);
  to = malloc(size * sizeof *to);

  for (i = 0; i < size; i++)
    from[i] = lrand48();
}

void seq_sort(int base, int n)
{
  int i, j, end_low, start_high;

  if (n <= 1)
    return;

  int pivot = from[base];
  j = base;

  for (i = base; i < base + n; i++)
    if (from[i] < pivot)
      to[j++] = from[i];
  end_low = j;
  
  for (i = base; i < base + n; i++)
    if (from[i] == pivot)
      to[j++] = from[i];
  start_high = j;
  
  for (i = base; i < base + n; i++)
    if (from[i] > pivot)
      to[j++] = from[i];

  for (i = base; i < base + n; i++)
    from[i] = to[i];

  seq_sort(base, end_low - base);
  seq_sort(start_high, n - (start_high - base));

#ifndef NDEBUG
  for (i = base + 1; i < base + n; i++)
    if (from[i] < from[i - 1])
      {
	fprintf(stderr, "missorted\n");
	exit(2);
      }
#endif
}

int main(int argc, char **argv)
{
  int i;

  setup(argc, argv);

  printf("starting sort...\n");
  selected_sort(0, size);
#ifdef DEBUG
  for (i = 0; i < size; i++)
    printf("%d\n", from[i]);
#endif
  return 0;
}
