#include "testharness.h"

//a macro from include/linux/kernel.h in the Linux kernel:
#define min(x,y) ({ \
	typeof(x) _x = (x);	\
	typeof(y) _y = (y);	\
	(void) (&_x == &_y);		\
	_x < _y ? _x : _y; })

double global = 5.0;

int main() {
  double res = min(global-1, min(global/2, global));

  if (res != 2.5) E(2);
  SUCCESS;
}
