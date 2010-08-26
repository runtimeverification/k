#include "testharness.h";

/* The error is triggered because CIL 1.3.7 introduces
   a loop back to _L. */

int main() {
	int x = 1, y = 0;
 _L:
	if (x && ++y > 1) E(1) else lbl:;
	SUCCESS;
}
