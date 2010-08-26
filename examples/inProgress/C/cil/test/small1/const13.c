/* Sourceforge bug #1850745 */

#include "string.h"

typedef struct
{
char p[5];
} t2;

void consttst1(const char *p);

void consttst2(const t2 * p2)
{
consttst1(p2->p[0]?p2->p:NULL);
}
