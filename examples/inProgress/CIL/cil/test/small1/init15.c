#include "testharness.h"

typedef struct {int x, y;} brlock_read_lock_t;

#define NR_CPUS           4
#define __BR_IDX_MAX      4
#define RW_LOCK_UNLOCKED { 5, 6 }

brlock_read_lock_t __brlock_array[NR_CPUS][__BR_IDX_MAX] =
     { [0 ... NR_CPUS-1] = { [0 ... __BR_IDX_MAX-1] = RW_LOCK_UNLOCKED } };

int main() {
  int i, j;
  for(i=0;i<NR_CPUS;i++) {
    for(j=0;j<__BR_IDX_MAX;j++) {
      if(__brlock_array[i][j].x != 5 ||
         __brlock_array[i][j].y != 6) {
        printf("At index [%d][%d] I found { %d, %d }\n",
               i, j, __brlock_array[i][j].x, __brlock_array[i][j].y);
        exit(1);
      }
    }
  }
  return 0;
}

