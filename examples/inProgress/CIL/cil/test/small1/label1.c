#define SEARCH(array, target) \
({ \
    __label__ found, retry; \
    typeof (target) _SEARCH_target = (target); \
    typeof (*array) *_SEARCH_array = (array); \
    int i, j;\
    int value;\
    int max = sizeof(array) / sizeof(*array);\
 retry: \
    for(i=0; i < max; i ++) \
       if(_SEARCH_array[i] == _SEARCH_target) { \
           value = i; goto found; \
       } \
    ({ __label__ found; goto found; \
       found: _SEARCH_target += 5; goto retry;}); \
  found : \
    value; \
}) 
    

int thearray[] = { 1, 3, 5, 7, 9, 11, 13, 15, 17, 21 };

int main() {
  __label__ endofblock;
  int res;
  
  res = -9 + (SEARCH(thearray, 7) /* 3 */ + SEARCH(thearray, 8) /* 6 */);
 endofblock:
  return res;
}
