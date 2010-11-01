#include "testharness.h"

int main() {
  struct l {
    struct l** next;
  } s[4];
  struct l* a;
  struct l* p[4];
  struct l* old;
  p[0] = s;
  p[0]->next = &p[0];
  old = (*p[0]->next);
  a = ((*p[0]->next) += 1);
  if (old + 1 != a)
    E(1);
  SUCCESS;
}
