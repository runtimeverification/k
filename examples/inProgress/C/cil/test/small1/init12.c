#include "testharness.h"

// From c-torture
struct empty { };
struct something {
	int spacer;
	struct empty foo;
	int bar;
};

struct something X = {
	foo: (struct empty) { },
	bar: 1,
};


int main() {
  if(X.bar != 1) E(1);
  if(X.spacer != 0) E(2);

  SUCCESS;
}
