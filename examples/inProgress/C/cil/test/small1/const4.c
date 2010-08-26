#include "testharness.h"

struct reiserfs_de_head {
  int x, y;
};

int somefunction() {
  return 8;
}
int main() {
  char empty_dir[sizeof(struct reiserfs_de_head ) * 2 +
                (strlen(".") + 8LL
                 - 1u & ~ (8LL - 1u)) +
                (strlen("..") + 8LL - 1u & ~ (8LL - 1u))];

  char another[somefunction()];
  
  printf("Sizeof empty_dir=%d\n", (int)sizeof(empty_dir));
  if(sizeof(empty_dir) != 32) E(1);

  printf("Sizeof another=%d\n", (int)sizeof(another));
  if(sizeof(another) != 8) E(2);

  
  SUCCESS;
}
