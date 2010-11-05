/* name:          array-size-trick.c
 * synopsis:      Check agreement of macro expansion and actual array
 *                size at compile time
 * author:        Dr. Christoph L. Spiel, Software&Systems GmbH
 * last revision: Do Okt 14 06:03:43 UTC 2004 */


#include <stdio.h>
#include <stdlib.h>

// This should be allowed !
extern struct foo udp_stats_in6[2 * 2];



/* Answer the number of elements in an array. */
#define numberof(m_array) (sizeof(m_array) / sizeof(m_array[0]))


#define ARRAY_LENGTH 3U


/* Define an array that *must* be exactly ARRAY_LENGTH elements
 * long.  In reality this lives in file "bar.h". */
int array[] = {9, 11, 13};


/* Here comes the "trick": declare a constant (that never will be
 * instantiated) twice.  The two declaration will be identical, if and
 * only if ARRAY_LENGTH == numberof(array), otherwise we get an error
 * at compile time.  In reality this also lives in file "bar.h". */
extern const int _guard[ARRAY_LENGTH - numberof(array)];
extern const int _guard[numberof(array) - ARRAY_LENGTH];

extern int test1[3 + 5];
extern int test1[4 + 4];

int
main(void)
{
    unsigned i;

    for(i = 0; i < ARRAY_LENGTH; i++)
    {
        printf("a[%u]: %d\n", i, array[i]);
    }

    return EXIT_SUCCESS;
}

