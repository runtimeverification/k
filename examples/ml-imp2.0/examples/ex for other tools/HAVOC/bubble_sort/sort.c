#include "../../../include/havoc.h"

typedef int *PINT;
__declare_havoc_bvar(_H_i);
__declare_havoc_bvar(_H_j);

#define array_elems(a,s,t) (__setminus(__array(a, sizeof(int), t) , __array(a, sizeof(int), s)))
#define all_array_elems(a,t) array_elems(a,0,t)
#define sorted(a,s) (__forall(__qvars(_H_i,_H_j), all_array_elems(a,s), _H_i <= _H_j ==> *_H_i <= *_H_j))


#define TRUE 1
#define FALSE 0

__requires(arr > 0)
__requires(__forall(_H_i, all_array_elems(arr,size), __type(_H_i, PINT)))
__requires(size > 0)
__ensures(sorted(arr,size))
__modifies (all_array_elems(arr,size))
void bubble_sort(int *arr, int size) {
  __loop_invariant(
		   __loop_modifies (all_array_elems(arr,size))
		   )	      
  while (TRUE) {
    int aux = 0;
    int i = 0;

    __loop_invariant (
		      __loop_assert(0 <= i && i < size)
		      __loop_assert(__forall(__qvars(_H_i,_H_j), array_elems(arr, aux, i+1), _H_i <= _H_j ==> *_H_i <= *_H_j))
		      __loop_modifies (all_array_elems(arr,size))
		      )
    while (i < size-1) {
      if (arr[i] > arr[i+1]) {
	int tmp = arr[i];
	arr[i] = arr[i+1];
	arr[i+1] = tmp;
	aux = i;
      }
      i++;
    }
    if (aux == 0) break;
  }
}

