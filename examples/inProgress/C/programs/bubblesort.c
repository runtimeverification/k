/* Copyright (c) 2010 the authors listed at the following URL, and/or
the authors of referenced articles or incorporated external code:
http://en.literateprograms.org/Bubble_sort_(C)?action=history&offset=20081229124806

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

Retrieved from: http://en.literateprograms.org/Bubble_sort_(C)?oldid=15710
*/


#include <stdio.h>

/* Swapping of elements in an array. Because there is a void* we need to give
this function the element_size of the to be sorted elements, we then can exchange the
array elements character by character. */
static void swap_fun (void *base, size_t element_size,
	                  int index1, int index2) {
	char *pc = base;
	char tmp;
	int i;
	for (i = 0; i < element_size; ++i) {
		tmp = pc[index1 * element_size + i];
        pc[index1 * element_size + i] = pc[index2*element_size + i];
        pc[index2 * element_size + i] = tmp;
	}
}


/* mimics the qsort interface */
void bubble_sort(void *base, size_t nmemb, size_t size,
                 int (*compar)(const void *, const void *)) {
  int i, j;
  char *pc =  base;
  char *pc_at_i;
  char *pc_at_j;

  for (i = nmemb -1; i > 0; --i){
    for (j = 0; j < i; ++j) {
	 /* we have to calculate the offsets, by defintion the size of
	 char is 1 in C, so we do not have to include  the size of the
	 elements while doing this address calculations */
      pc_at_i = pc + (i * size);
      pc_at_j = pc + (j * size);
      if (compar (pc_at_i, pc_at_j) <  0) {
		  swap_fun(base, size, i, j);
      }
    }
  }
}


int int_cmp_fun (const void * v1, const void * v2) {
  const int * i1 = v1;
  const int * i2 = v2;
  int result;
  if (*i1 == *i2) {
    result = 0;
  } else if (*i1 < *i2) {
    result = -1;
  } else {
    result = 1;
  }
  return result;
}


static void print_int_arr(int *arr, size_t size_of_arr) {
  int i;
  for (i = 0; i < size_of_arr; i++) {
    printf("%d ", arr[i]);
  }
  putchar('\n');
}


int main(void) {
  enum { T_SIZE = 7};
  int arr[T_SIZE] = {-1, 2, 1, 3, 5, -10, -11};

  printf("array before sorting: ");
  print_int_arr(arr, T_SIZE);
  printf("array after bubblesort: ");
  bubble_sort(arr, T_SIZE, sizeof(int), int_cmp_fun);
  print_int_arr(arr, T_SIZE);
  return 0;
}


