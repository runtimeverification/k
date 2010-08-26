#include <stdio.h>
#include <stdlib.h>

#ifdef _GNUCC
#include <unistd.h>     // dup, close
#endif
#ifdef _MSVC
#include <io.h>
#endif

//#include "main.h"
/****** Data sizes *******
* U8  must be an unsigned of 8 bits
* U16 must be an unsigned of 16 bits *
* U32 must be an unsigned of 32 bits *
* U64 must be an unsigned on 64 bits *
* UPOINT must be an unsigned of the size of a pointer
* ALIGN must be the number of bytes the data accesses must be aligned to - 1
*       i.e. it must be 3 for the data to be aligned on a 32-bit boundary. It
*       must be at least 1 (16-bit alignment). It must be <= UPOINT
* ALSHIFT is log2(ALIGN + 1)
* UALIGN is the integer whose size if ALIGN + 1.
*************************/

typedef unsigned long UL;
typedef unsigned char UC;
typedef int BOOL;
#define  TRUE  1
#define  FALSE 0

#define MASK(bitlen) ((1 << (bitlen)) - 1)

#ifdef alpha_UNIX	      /* Both GCC and DEC cc seem to have the same */
#define ALSHIFT  3
#define ALIGN    MASK(ALSHIFT)
#define UALIGN   U64

#define U8     unsigned char
#define S8     char
#define U16    unsigned short
#define S16    short
#define U32    unsigned int
#define S32    int
#define U64    unsigned long
#define S64    long
#define UPOINT U64
#define SPOINT S64
#define DIRLISTSEP ':'
#endif /* alpha_UNIX */

#ifdef x86_WIN32
#define ALSHIFT 2
#define ALIGN   MASK(ALSHIFT)
#define UALIGN  U32

#define U8     unsigned char
#define S8     char
#define U16    unsigned short
#define S16    short
#define U32    unsigned long
#define S32    long
#define UPOINT U32
#define SPOINT S32
 
#define DIRLISTSEP ';'

#ifdef _MSVC  /* MSVC on x86 */
#define U64    unsigned __int64
#define S64    __int64
#endif /* _MSVC */

#ifdef _GNUCC  /* GNU CC on x86 */
#define U64    unsigned long long
#define S64    long long
#endif /* _GNUCC */ 

#endif /* x86_WIN32 */

#ifdef x86_LINUX
#define ALSHIFT 2
#define ALIGN   MASK(ALSHIFT)
#define UALIGN  U32
#define __cdecl

#define U8     unsigned char
#define S8     char
#define U16    unsigned short
#define S16    short
#define U32    unsigned long
#define S32    long
#define UPOINT U32
#define SPOINT S32
#define U64    unsigned long long
#define S64    long long
#define DIRLISTSEP ':'
#endif /* x86_WIN32 */

#define _ASSERT(be) {if(!(be)){fprintf(stderr,"Assertion failed on line %d in file %s\n", __LINE__, __FILE__);exit(2);}}

#define ERR_SET         
#define ERR_CHECK(v,stop,prg) 
#define EXIT(v, n)      exit(n)

#define ERRLINE    {fprintf(stderr, "Error at %s(%d):",__FILE__,__LINE__);\
		    ERR_SET;}
#define WARNLINE   {fprintf(stderr, "Warning at %s(%d):",__FILE__,__LINE__);}

#define ERROR0(v, txt)              {ERRLINE;\
			  	     fprintf(stderr,txt);EXIT(v,1);}
#define ERROR1(v, txt, d1)          {ERRLINE;\
				     fprintf(stderr,txt, d1);EXIT(v,1);}

typedef long clock_t;
 clock_t __cdecl clock(void);
 int    __cdecl rand(void);
#ifdef _MSVC
#       define CLOCKS_PER_SEC 1000
#else
#       define CLOCKS_PER_SEC  1000000
#endif


#define TIMESTART(clk) {clk=(double)clock();}
#define TIMESTOP(clk)  {clk=1000000.0 * ((double)clock()-(clk))/CLOCKS_PER_SEC;}


extern  int   debugMM;      

#define SETDBGOUT   int _stdout; fflush(stdout);_stdout=dup(1);dup2(2,1);
#define RESTOREOUT  fflush(stdout); dup2(_stdout, 1); close(_stdout);


extern  char* __stackInit;
extern  int   __mmId;
#define STACK_CHECK(category) { char __probe;\
                      long _pDepth = __stackInit - & __probe;\
                      __MM_REPORT("stack", &__probe, _pDepth, category);}

#define STACK_INIT { char __probe;\
                     __stackInit = & __probe; __mmId = 0; }

#define MALLOC(mallocfun, res, err, sz, type, category) {\
       long _sz = (sz);\
       (res) = (type)mallocfun(_sz);\
       if(! (res)) {\
           ERROR0(err, "Cannot malloc\n"); \
       }\
       __MM_REPORT("malloc", (res), _sz, category);}

#define FREE(freefun, res, category) {\
       if(res) {\
        __MM_REPORT("free", (res), 0, category);\
        freefun(res); }}

#define CALLOC(callocfun, res, err, nrelem, sz, type, category) {\
       int _nrelem = (nrelem);\
       long _sz = (sz);\
       (res) = (type)callocfun(_nrelem, _sz);\
       if(! (res)) {\
           ERROR0(err, "Cannot calloc\n"); \
       }\
       __MM_REPORT("malloc", (res), _sz * _nrelem, category);}

#define REALLOC(res, err, sz, type, category) {\
       long _sz = (sz);\
       if((res)) { __MM_REPORT("free", (res), 0, category); }\
       (res) = (type)realloc((res), _sz);\
       if(! (res)) {\
           ERROR0(err, "Cannot realloc\n"); \
       }\
       __MM_REPORT("malloc", (res), _sz, category);}

#define STRDUP(res, err, what, category) {\
       char* _what = what;\
       long _sz = strlen(_what) + 1;\
       (res) = strdup(_what);\
       if(! (res)) {\
           ERROR0(err, "Cannot strdup\n"); \
       }\
       __MM_REPORT("malloc", (res), _sz, category);}
    
#if defined(_DEBUG) || defined(_DEBUGMM)
#define __MM_REPORT(what, where, size, category) {\
       if(debugMM) {\
        SETDBGOUT; \
        printf("*MM%d: %-6s 0x%08lx %08ld %-20s %s:%d\n", \
                __mmId ++, \
                (what), (where), (long)(size), (category),__FILE__,__LINE__);\
        RESTOREOUT; } \
        }
#else
#define __MM_REPORT(what, where, size, category) { }
#endif

//#include "hash.h"
typedef int HASH_KEY;





#ifdef SMALLMEM
#define  BUCKETS_SHIFT 5
#define  BUCKET_SIZE 4
#else
#define  BUCKETS_SHIFT 8
#define  BUCKET_SIZE 8
#endif

#define  NR_HASH_BUCKETS (1 << (BUCKETS_SHIFT))  /* These must be 2^k */


			      /* A Hash entry holds a particular pair (key, 
                               * data)  */
#define EMPTY_ENTRY           0x54854A33

typedef struct HashEntry {
  int key;                    /* The key EMPTY_ENTRY is reserved for empty 
                               * entries  */
  void * data;
} HASH_ENTRY;

			      /* A bucket is a list of clusters of 
                               * HASH_ENTRIES. It behaves like a list of 
                               * entries but it is optimized by allocating 
                               * a cluster of entries at a time */
typedef struct BucketData {
  struct BucketData * next;
  HASH_ENTRY entries[BUCKET_SIZE];
} BUCKET_DATA;


typedef struct {
  int size;
  BUCKET_DATA * data;
} HASH_BUCKET;


typedef HASH_BUCKET *  PHASH;


PHASH NewHash(void);
void  FreeHash(PHASH);

			      /* The following functions return TRUE if the 
                               * particular data was already in the hash */
int   HashLookup(PHASH, HASH_KEY, void *  *  data);
			      /* If data already exists, then replace it */
int   AddToHash(PHASH, HASH_KEY, void * );

                              /* Nothing happens if the key does not exits */
int   DeleteFromHash(PHASH, HASH_KEY);

                              /* Maps a function to a hash table. The last 
                               * element is a closure. The data is 
                               * overwritten but not placed into another 
                               * bucket ! */
int   MapHash(PHASH, void *  (* )(HASH_KEY, void * , UPOINT),
              UPOINT);

                              /* Returns the number of elements in the table */
unsigned int   SizeHash(PHASH);
                              /* Preallocates some hashes */
int   preallocateHashes(void);
                              /* And release them */
int   releaseHashes(void);
// End hash.h


unsigned SizeHash(PHASH hash) {
  int i;
  HASH_BUCKET *  pBucket = (HASH_BUCKET * )hash;
  unsigned res = 0;
  for(i=0;i<NR_HASH_BUCKETS;i++, pBucket++) {
    res += pBucket->size;
  }
  return res;
}
                              /* A hash table is actually an array of 
                               * NR_HASH_BUCKETS * HASH_BUCKET */

			      /* Converts a hash key to a bucket index */
#define HashKeyToBucket(k, res) { unsigned int _t = (unsigned int)k;\
                                  res = 0;\
                                  for(res = 0;_t;_t >>= BUCKETS_SHIFT) {\
                                       res ^= (_t & (NR_HASH_BUCKETS - 1));\
			        }}


                              /* Keep a list of pre-allocated buckets */
#define BUCKET_CACHE_SIZE      (2 * NR_HASH_BUCKETS)

#ifdef SMALLMEM
#define BUCKET_CACHE_PREALLOC  (BUCKET_CACHE_SIZE >> 2)
#else
#define BUCKET_CACHE_PREALLOC  BUCKET_CACHE_SIZE
#endif

static  BUCKET_DATA *  bucketCache[BUCKET_CACHE_SIZE];
static  int nextFreeBucket = 0;


static  BUCKET_DATA *  acquireHashBucket(void) {
  if(nextFreeBucket == 0) {
    BUCKET_DATA *  buck;
    MALLOC(malloc, buck, NULL, sizeof(BUCKET_DATA), BUCKET_DATA*,
           "hash_bucket_data");
    return buck;
  } else {
    return bucketCache[-- nextFreeBucket];
  }
}

static int releaseHashBucket(BUCKET_DATA *  buck) {
  if(nextFreeBucket < BUCKET_CACHE_SIZE) {
    bucketCache[nextFreeBucket ++] = buck;
  } else {
    FREE(free, buck, "hash_bucket_data");
  }
  return 0;
}

int     preallocateHashes(void) {
  int i;
  nextFreeBucket = 0; /* So that acquire does not steal our buckets  */
  _ASSERT(BUCKET_CACHE_PREALLOC <= BUCKET_CACHE_SIZE);
  for(i=0;i<BUCKET_CACHE_PREALLOC;i++) {
    bucketCache[i] = acquireHashBucket();
  }
  nextFreeBucket = i;
  return 0;
}

int   releaseHashes(void) {
  int i;
  for(i=0;i<nextFreeBucket;i++) {
    FREE(free, bucketCache[i], "hash_bucket_data");
  }
  nextFreeBucket = 0;
  return 0;
}

/**************** NewHash *******************/
PHASH NewHash(void) {
  /* Allocate a hash */
  PHASH res = (PHASH)calloc(NR_HASH_BUCKETS, sizeof(HASH_BUCKET));
  if(! (res)) {
    ERROR0(err, "Cannot calloc\n"); 
  }
  return (PHASH)res;
}

void FreeHash(PHASH hin) {
  int i;
  HASH_BUCKET *  h = (HASH_BUCKET * )hin;
  for(i=0;i<NR_HASH_BUCKETS;i++) {
    HASH_BUCKET *  buck = & h[i];
    BUCKET_DATA *  bdata = buck->data;
    while(bdata != NULL) {
      BUCKET_DATA *  t_bdata = bdata;
      bdata = bdata->next;
      releaseHashBucket(t_bdata);
    }
  }
  FREE(free, h, "hash_table");
}

typedef enum {SET, LOOKUP, DELETE} HashOper;

static void *   ProcessHash(PHASH hin, HASH_KEY key, void *  data,
                                int *  found, HashOper oper) {
  int bucket_no, i, k;
  BUCKET_DATA *  buck = NULL;
  BUCKET_DATA *  *  next = NULL;
  HASH_ENTRY *target = NULL;
  HASH_BUCKET *  h = (HASH_BUCKET * )hin;
  
  if(key == EMPTY_ENTRY) { key ++; }
  
  _ASSERT(h);

  HashKeyToBucket(key, bucket_no);	/* Get the bucket number */
  next = & h[bucket_no].data;

  i = BUCKET_SIZE;
  for(k=h[bucket_no].size;k > 0;) { /* Look for the data */
    HASH_ENTRY *  e;
    buck = *next;             /* Get the next cluster */ 
    next = &(buck->next);     /* Move one to next cluster */
    e = buck->entries;        /* This is the current entry */
    for(i=0;i < BUCKET_SIZE && k > 0; k--, i++, e++) {
      if(!target && e->key == EMPTY_ENTRY) target = e;
      if(e->key == key) {
	*found = 1;
        switch(oper) {
        case SET: e->data = data; return e->data;
        case LOOKUP: return e->data;
        case DELETE: e->data = NULL; e->key = EMPTY_ENTRY; return NULL; 
	}
      }
    }
    if(k == 0)  /* Not in the bucket, hence not in table */
      break;
    _ASSERT(i == BUCKET_SIZE);
  }
  _ASSERT(k == 0);
  *found = 0;		      /* Here if not found */
  if(oper != SET) {
    return NULL;
  }
  if(! target) {
			      /* Must create a new entry */
    if(i == BUCKET_SIZE) {		     
      if(! next) {
        next = &(h[bucket_no].data);
      }
      _ASSERT(*next == NULL);
      buck = acquireHashBucket();
      *next = buck;
      buck->next = NULL;
      i = 0;
    }
    target = &buck->entries[i];
    h[bucket_no].size ++;
  }
  target->key = key;
  target->data = data;
  return NULL;
}

			      /* Lookup a hash key. Put the result in *data */
int HashLookup(PHASH h, HASH_KEY key, void *  *  data) {
  int found;
  *data = ProcessHash(h, key, NULL, &found, LOOKUP);
  return found;
}

			      /* Extend the hash. If the data already exists 
                               * then replace it*/
int AddToHash(PHASH h, HASH_KEY key, void*  data) {
  int found;
  ProcessHash(h, key, data, &found, SET);
  return found;
}

int DeleteFromHash(PHASH h, HASH_KEY key) {
  int found;
  ProcessHash(h, key, NULL, &found, DELETE);
  return 0;
}

int MapHash(PHASH h, void*  (*  f)(HASH_KEY, void* , UPOINT),
            UPOINT closure) {
  int i;
  HASH_BUCKET *  pBucket = (HASH_BUCKET*  )h;

  for(i=0;i<NR_HASH_BUCKETS;i++, pBucket ++) {
    int sz = pBucket->size;
    BUCKET_DATA *  pData = pBucket->data;
    HASH_ENTRY *  pEntry = pData->entries;
    int k = 0;
    for(;sz > 0;sz --, k++, pEntry++) {
      if(k == BUCKET_SIZE) {
        k = 0;
        pData  = pData->next;
        pEntry = pData->entries;
      }
      if(pEntry->key == EMPTY_ENTRY)
        continue;
      pEntry->data = (*f)(pEntry->key, pEntry->data, closure);
    }
  }
  return 0;
}








/* Some globals that PCC needs */
int error_level, anerror;
void myexit(int n) {
  exit(n);
}
#ifdef _MSVC
#define random rand
#else
/* extern int random(void); -- Weimer: not needed! */
#endif
int __mmId;
int debugMM;
int debug;


#ifndef ITERS
  #define ITERS 50000
#endif



int main() {
  /* Test hash tables */
  PHASH h = NewHash();
  int i;
  double clk;
  int count = 0;
  int sz;
  
  /* Add and delete random numbers from the hash table */
  TIMESTART(clk);
  for(i=0;i<ITERS;i++) {
    int k = random() & 0x7FFFL;
    AddToHash(h, k, (void* )k);
  }
  for(i=0;i<ITERS;i++) {
    int k = random() & 0x7FFFL;
    void *data = NULL;
    if(HashLookup(h, k, & data)) {
      count ++;
    }
  }
  sz = SizeHash(h);
  FreeHash(h);
  TIMESTOP(clk);
  printf("Hash has %d elements. Found %d times\n",
          sz, count);
  printf("Run hashtest in %8.3lfms\n", clk / 1000.0);
  exit (0);
}


