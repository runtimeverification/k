#include <stddef.h>
#include "testharness.h"

typedef struct mystruct {
	int a;
	int b;
} Mystruct;

Mystruct Foo;

int main() {
    long addr_b;

    addr_b = (long)&Foo;

    addr_b += (long)offsetof(Mystruct, b); 

    if (addr_b != (long)&Foo.b) E(1);

    SUCCESS; 
}
