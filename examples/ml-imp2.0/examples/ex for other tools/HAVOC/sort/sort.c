#include "../../../include/havoc.h"

typedef int *PINT;

//bound vars
__declare_havoc_bvar_type(_H_i, int*);
__declare_havoc_bvar_type(_H_j, int*);

//// macros start //////////
#define array_elems(a,s,t) (__setminus(__array(a, sizeof(int), t) , __array(a, sizeof(int), s)))
#define all_array_elems(a,t) array_elems(a,0,t)

#define sorted(a,s) (__forall(__qvars(_H_i,_H_j), all_array_elems(a,s), _H_i <= _H_j ==> *_H_i <= *_H_j))

#define back_gt(a,s,i) (__forall(_H_i, all_array_elems(a,i), __forall(_H_j, array_elems(a,i,s), *_H_i <= *_H_j)))
#define arr_min(a,i,j,min) (__forall(_H_i, array_elems(a,i,j), a[min] <= *_H_i))
//// macros end //////////



__requires(arr > 0)
__requires(__forall(_H_i, all_array_elems(arr,size), __type(_H_i, PINT)))
__requires(size > 0)
__ensures(sorted(arr,size))
__modifies (all_array_elems(arr,size))
void selection_sort(int *arr, int size) {
  int i;
  int j, min,tmp;
  
  i = 0;
  min = 0;
  __loop_invariant (
		   __loop_assert(i >= 0)
		   __loop_assert(i <= size)
		   __loop_assert(sorted(arr,i))
		   __loop_assert(back_gt(arr,size,i))
		   __loop_modifies (all_array_elems(arr,size))
		   )
  for (; i < size; i++) {
    min = i;
    j = i;

    __loop_invariant (
		      __loop_assert(i <= j)
		      __loop_assert(j <= size)
		      __loop_assert(i <= min)
		      __loop_assert(min <= j)
		      __loop_assert(min < size)
		      __loop_assert(arr_min(arr,i,j,min))
		      __loop_modifies(all_array_elems(arr,size))
		      )
    // find min elem in [i,size)
    for (; j < size; j++) {
      if (arr[j] < arr[min]) {
	min = j;
      }
    }

    // swap elems at i and min
    tmp = arr[i];
    arr[i] = arr[min];
    arr[min] = tmp;

  }
}

