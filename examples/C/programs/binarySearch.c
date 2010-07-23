/* Copyright (c) 2010 the authors listed at the following URL, and/or
the authors of referenced articles or incorporated external code:
http://en.literateprograms.org/Binary_search_(C)?action=history&offset=20090509134350

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

Retrieved from: http://en.literateprograms.org/Binary_search_(C)?oldid=16429
*/

#include <stdio.h>
#include <stdlib.h>

int binary_search(int a[], int low, int high, int target) {
	int origLow = low;
	int origHigh = high;
    while (low <= high) {
        int middle = low + (high - low)/2;
        if (target < a[middle])
            high = middle - 1;
        else if (target > a[middle])
            low = middle + 1;
        else
            return middle;
    }
	printf("Couldn't find %d in array:\n", target);
	for (int i = origLow; i < origHigh; i++){
		printf("a[%d] = %d\n", i, a[i]);
	}
    return -1;
}

void insertion_sort(int a[], int length)
{
  int i;
  for (i=0; i < length; i++)
  {
      /* Insert a[i] into the sorted sublist */
      int j, v = a[i];
      for (j = i - 1; j >= 0; j--)
      {
          if (a[j] <= v) break;
          a[j + 1] = a[j];
      }
      a[j + 1] = v;

  }
}

int main(void) {
    int num_elements = 15;
    int* a = (int*)malloc(num_elements*sizeof(int));
    int i;
    for(i=0; i<num_elements; i++) {
        do {
            a[i] = rand() % num_elements;
        } while(a[i] == num_elements/7);
    }
	insertion_sort(a, num_elements);

    for(i=0; i<10; i++) {
        int present_val = a[rand() % num_elements];
		//printf("VOLATILE looking for %d, ", present_val);
        int found_at = binary_search(a, 0, num_elements - 1, present_val);
		//printf("VOLATILE found %d\n", a[found_at]);
		if (present_val == a[found_at]){
			printf("present_val == a[found_at]\n");
		} else {
			printf("looking for %d, ", present_val);
			printf("found %d\n", a[found_at]);
			printf("BUG present_val == a[found_at]\n");
		}
    }
    return 0;
}

