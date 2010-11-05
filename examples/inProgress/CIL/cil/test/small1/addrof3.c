#include "testharness.h"

struct qstr {
	const unsigned char * name;
	unsigned int len;
	unsigned int hash;
};

struct qstr *foo(const struct qstr *p) {
  return p;
}

int main() {

  struct qstr *x = foo(&(const struct qstr) { "socket:", 7, 0 });
  if(x->name[1] != 'o') E(1);

  if(x->len != 7) E(2);

  SUCCESS;
}
