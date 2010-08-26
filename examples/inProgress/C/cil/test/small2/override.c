#include "../small1/testharness.h"
#include "../small1/testkinds.h"

// NUMERRORS 5

int * __SAFE global_variable_1;

typedef struct {
  int * __SAFE field_1;
  int *field_2;
  int *field_3;
} my_struct; 

my_struct *global_variable_2;

int main() {
  int * __SAFE local_variable_1;

#if ERROR == 1
  local_variable_1 = 55;
  if(!(HAS_KIND(local_variable_1, SAFE_KIND))) E(1); //ERROR(1):Error 1
#endif
#if ERROR == 2
  global_variable_1 = 55;
  if(!(HAS_KIND(global_variable_1, SAFE_KIND))) E(2); //ERROR(2):Error 2
#endif
#if ERROR == 3
  global_variable_2 = global_variable_1;
  if((HAS_KIND(global_variable_1, WILD_KIND))) E(3); //ERROR(3):Error 3
#endif
#if ERROR == 4
  global_variable_2 = global_variable_1;
  if((HAS_KIND(global_variable_2, WILD_KIND))) E(4); //ERROR(4):Error 4
#endif
#if ERROR == 5
  global_variable_2 = &global_variable_1;
  if((HAS_KIND(global_variable_2->field_1, WILD_KIND))) E(5); //ERROR(5):Error 5
#endif
  SUCCESS;
}
