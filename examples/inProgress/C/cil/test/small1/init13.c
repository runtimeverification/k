// From c-torture
#include "testharness.h"

typedef struct
{
  char *key;
  char *value;
} T1;

typedef struct
{
  long type;
  char *value;
} T3;

T1 a[] =
{
  {
    "",
    ((char *)&((T3) {1, (char *) 1}))
  }
};


int main() {
  T3 *t3;
  
  if(sizeof(a) != sizeof(T1)) E(1);

  if(a[0].key[0]) E(2);

  t3 = a[0].value;
  if(t3->type != 1) E(3);
  if(t3->value != 1) E(4);


  SUCCESS;
}

