#define U8     unsigned char
#define S8     char
#define U16    unsigned short
#define S16    short
#define U32    unsigned long
#define S32    long
#define UPOINT U32
#define SPOINT S32

typedef UPOINT ITEM;
typedef UPOINT ITEMADDR;
#define NULLITEM (ITEM)0

                              /* The number of bits in an ITEM */
#define BITS_IN_ITEM (sizeof(ITEM) * 8)

/* The least-significant 3 bits of an ITEM are reserved for a tag that 
 * encodes whether the ITEM is a variable, a constant, an integer, an 
 * application or an abstraction. */

#define TAG_BITS 3
#define TAG       MASK(TAG_BITS)

			      /* Reserve tags with the two least significant 
                               * bits for pointers */
#define INDIRECT 0
#define VAR      1	      
#define INT      2
#define CONST    3	      
#define NOTAG    4	     /* Used for indirections on 32-bit machine. 
                              * Everything before this fits completely in an 
                              * ITEM */ 
#define ABS      5            /* See ISAPPLORABS */
#define COMM     6
#define APPL     7            /* See ISAPPLORABS */


#define LFWORD_SIZE    16
#define DISK_TAG_BITS   4

#define MIN(x,y) ((x)<(y)?(x):(y))
#define MAX(x,y) ((x)>(y)?(x):(y))
#define ABSVAL(x)   (((S32)(x)) >= 0 ? ((S32)(x)) : (- ((S32)(x))))

#define INT_SIZE  MIN(BITS_IN_ITEM - TAG_BITS, 2 * LFWORD_SIZE - DISK_TAG_BITS)

/* Use GETINT(item) to get the integer represented by item */
#define GETINT(it) ((int)(((SPOINT)(it)) >> TAG_BITS))

#define ZERO       INT        /* Only the tag */
#define MAX_INT    ((int)((1  << (INT_SIZE - 1)) - 1))
#define MIN_INT    ((int)(- 1 - MAX_INT))

			      /* Make an integer */
#define EXTRACTSIGNED(n,start,bits) \
    (((n) << (8*sizeof(int) - (start) - (bits))) >> (8*sizeof(int) - (bits)))

ITEM CONS_HEAD(int tag);
void CONS_NEXT(ITEM head, ITEM i);
#define  LONGINT_CONST    12

extern void exit(int);
extern ITEM builtIn[];
                              /* Build an integer */
ITEM CONS_INT(int n) {
  if((n < MIN_INT) || (n > MAX_INT)) {
    return 0;
  } else {
    return (ITEM)(INT | (((SPOINT)n) << TAG_BITS));
  }
}


int test(int n, int m) {
  if(n < (- 5 - (unsigned)m)) {  // The comparison should be unsigned !!
    if(m < (int)(- 5 - (unsigned)n)) {  // The comparison should be signed !!
      return n;
    } else
      return n + m;
  } else {
    return m;
  }
}


int foo(int n, int m) {
  if (n < (1 << sizeof(ITEM))) /* The ISO says that this should be signed 
                                * comparison. MSVC uses unsigned !!!  */
    return n;
  else
    return m;
}
