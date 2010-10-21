// this include was added to the tests by running:    for fil in *.c; do sed -i '1i#include "fsl-header.h"' $fil; done
// the below assumes size_t, and in GCC __SIZE_TYPE__, are long unsigned ints, as in 20020406-1.c
// it would be idea for the tests to include precisely what they need, but this allows us to add dependencies as we discover them
#define size_t long unsigned int
void exit(int);
void abort(void);
void* malloc(size_t);
void* malloc(size_t);
void free(void*);
int strcmp(const char *, const char *);
void* memset(void *, int value, size_t);
#undef size_t
