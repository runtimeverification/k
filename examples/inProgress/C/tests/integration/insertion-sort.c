/* Copyright (c) 2010 the authors listed at the following URL, and/or
the authors of referenced articles or incorporated external code:
http://en.literateprograms.org/Insertion_sort_(C)?action=history&offset=20081205204844

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

Retrieved from: http://en.literateprograms.org/Insertion_sort_(C)?oldid=15530
*/

void insertion_sort(int a[], int length);
int checkThatArrayIsSorted (int array[], int length);

/* Sort an array of integers */
void insertion_sort(int a[], int length)
{
  int i;
  for (i=1; i < length; i++)
  {
      /* Insert a[i] into the sorted sublist */
      int j, v = a[i];

      for (j = i - 1; j > 0; j--)
      {
          if (a[j] <= v) break;
          a[j + 1] = a[j];
      }
      a[j + 1] = v;

  }
}

int checkThatArrayIsSorted (int array[], int length)
{
	int sorted = 0;
    int i;
    for (i = 1; i < length; i+=1)
    {
       if (array[i-1] <= array[i])
       {
          sorted++;
          //printf("The array is not in sorted order at position %d\n", i-1);
       }
    } 
	return sorted;
}


int main(void)
{
    unsigned int i;
    int a[] = {5,1,9,3,2};
    insertion_sort(a, sizeof(a)/sizeof(*a));
    /* Print out a */
    for(i=0; i<sizeof(a)/sizeof(*a); i++)
    {
        //printf("%d\n", a[i]);
    }

    return checkThatArrayIsSorted(a, sizeof(a)/sizeof(*a));
}


