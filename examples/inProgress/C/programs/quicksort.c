/* Copyright (c) 2010 the authors listed at the following URL, and/or
the authors of referenced articles or incorporated external code:
http://en.literateprograms.org/Quicksort_(C)?action=history&offset=20070511214343

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

Retrieved from: http://en.literateprograms.org/Quicksort_(C)?oldid=10011
*/

#ifndef _QUICKSORT_H_
#define _QUICKSORT_H_

#include <stdio.h>
#include <stdlib.h>

void quicksort(void * base, size_t num_elements, size_t element_size,
               int (*comparer)(const void *, const void *));

#endif


#define MIN_QUICKSORT_LIST_SIZE    2

static int compare_elements_helper(void *base, size_t element_size, int idx1, int idx2,
                                   int(*comparer)(const void *, const void*))
{
    char* base_bytes = base;
    return comparer(&base_bytes[idx1*element_size], &base_bytes[idx2*element_size]);
}

#define element_less_than(i,j)  (compare_elements_helper(base, element_size, (i), (j), comparer) < 0)

static void exchange_elements_helper(void *base, size_t element_size, int idx1, int idx2)
{
    char* base_bytes = base;
    int i;
    for (i=0; i<element_size; i++)
    {
        char temp = base_bytes[idx1*element_size + i];
        base_bytes[idx1*element_size + i] = base_bytes[idx2*element_size + i];
        base_bytes[idx2*element_size + i] = temp;
    }
}

#define exchange_elements(i,j)  (exchange_elements_helper(base, element_size, (i), (j)))

void insertion_sort(void * base, size_t num_elements, size_t element_size,
                    int (*comparer)(const void *, const void *))
{
   int i;
   for (i=0; i < num_elements; i++)
   {
       int j;
       for (j = i - 1; j >= 0; j--)
       {
           if (element_less_than(j, j + 1)) break;
           exchange_elements(j, j + 1);
       }
   }
}

int partition(void * base, size_t num_elements, size_t element_size,
               int (*comparer)(const void *, const void *), int pivotIndex)

{
    int low = 0, high = num_elements - 1;
    exchange_elements(num_elements - 1, pivotIndex);
	// num_elements = 16
	// low = 0
	// high = -1
	// pivotIndex = 9
/*
	 a) num_elem = 16, pivotIndex = 9, low = 0, high = 15\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 15\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 14\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 13\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 12\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 11\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 10\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 9\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 8\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 7\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 6\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 5\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 4\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 3\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 2\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 1\n
	 e) num_elem = 16, pivotIndex = 9, low = 0, high = 0\n
	 
 "Int" 14(.List{K}) |-> "Int" 9(.List{K}) 
  "Int" 15(.List{K}) |-> "Int" 4(.List{K}) 
  "Int" 16(.List{K}) |-> "Int" 3(.List{K}) 
  "Int" 17(.List{K}) |-> "Int" 0(.List{K}) 
  "Int" 18(.List{K}) |-> "Int" 3(.List{K}) 
  "Int" 19(.List{K}) |-> "Int" 5(.List{K}) 
  "Int" 20(.List{K}) |-> "Int" 14(.List{K}) 
  "Int" 21(.List{K}) |-> "Int" 15(.List{K}) 
  "Int" 22(.List{K}) |-> "Int" 15(.List{K}) 
  "Int" 23(.List{K}) |-> "Int" 13(.List{K}) 
  "Int" 24(.List{K}) |-> "Int" 2(.List{K}) 
  "Int" 25(.List{K}) |-> "Int" 3(.List{K}) 
  "Int" 26(.List{K}) |-> "Int" 8(.List{K}) 
  "Int" 27(.List{K}) |-> "Int" 1(.List{K}) 
  "Int" 28(.List{K}) |-> "Int" 3(.List{K}) 
  "Int" 29(.List{K}) |-> "Int" 0(.List{K}) 

*/
    while (1) {
		while (element_less_than(low, num_elements-1) && low < num_elements-1) {
			low++;
		}
		while ((!element_less_than(high, num_elements-1)) && high > 0) {
			//printf("a) num_elem = %d, pivotIndex = %d, low = %d, high = %d\n", num_elements, pivotIndex, low, high);
			high--;
			// if (high < 0) {
				// debug(0);
			// }
		}
		if (low >= high) {
			break;
		}
		exchange_elements(low, high);
    }
    exchange_elements(low, num_elements - 1);
    return low;
}

void quicksort(void * base, size_t num_elements, size_t element_size,
               int (*comparer)(const void *, const void *))
{
    int pivotIndex;

    if (num_elements < MIN_QUICKSORT_LIST_SIZE) {
        insertion_sort(base, num_elements, element_size, comparer);
        return;
    }

    pivotIndex = rand() % num_elements;

    pivotIndex = partition(base, num_elements, element_size, comparer, pivotIndex);

    quicksort(base, pivotIndex, element_size, comparer);
    quicksort(((char*)base) + element_size*(pivotIndex+1),
              num_elements - (pivotIndex + 1), element_size, comparer);

}


int compare_int(const void* left, const void* right) {
    return *((int*)left) - *((int*)right);
}

int main(void) {
    //int size = atoi(argv[1]);
	int size = 8;
    int* a = malloc(sizeof(int)*size);
    int i;
    //srand(1);

    for(i=0; i<size; i++) {
        a[i] = rand() % size;
    }
    quicksort(a, size, sizeof(int), compare_int);
    for(i=1; i<size; i++) {
        if (!(a[i-1] <= a[i])) {
            puts("ERROR");
            return -1;
        }
    }
    puts("SUCCESS");
    return 0;
}

