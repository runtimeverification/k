#include "../small1/testharness.h"

// This test checks malloc on compatible pointers.
// NUMERRORS 3

#include <malloc.h>

int main(void)
{
    int *p1 = malloc(sizeof(*p1));
    int * __FSEQ * __COMPAT p2 = malloc(10 * sizeof(*p2));
    int i;

    // Check initialization.
    *p1 = *p2[9]; // ERROR(1)

    *p1 = 42;

    for (i = 0; i < 10; i++)
    {
        p2[i] = p1;
    }

    // Check alloc bounds.
    p2[10] = &x; // ERROR(2)

    // Check bounds of pointer in array.
    *(p2[5] + 1) = 4242; // ERROR(3)

    // Check contents of pointers.
    if (**p2 != 42) E(3);

    // Check aliasing of pointers.
    **p2 = 4242;
    if (*p2[9] != 4242) E(4);

    SUCCESS;
}
