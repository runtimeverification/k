typedef struct { int counter; } atomic_t;

#define TYPE0 volatile struct { int a[100]; }
#define TYPE1 volatile int 

static __inline__ void atomic_add(int i, volatile atomic_t *v)
{
        __asm__ __volatile__(
		""  "addl %1,%0"
		:"=m" ((*(TYPE0 *) v ) )
		:"ir" (i), "m" ((*(TYPE0 *) v ) ));
}
