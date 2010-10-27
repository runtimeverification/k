#if defined(__BLOCKS__) && defined(__clang__)
// rdar://8241648
void *malloc(__SIZE_TYPE__ size);
extern void abort (void);

typedef struct bigbig {
   int array[512];
   char more[32];
} BigStruct_t;

BigStruct_t (^global)(void) = ^{ return *(BigStruct_t *)malloc(sizeof(struct bigbig)); };

const char * getBlockSignature(void *);
 
BigStruct_t foo(int param) {
   BigStruct_t x;
   BigStruct_t (^f)(int) = ^(int param) {
     BigStruct_t *result = malloc(sizeof(BigStruct_t));
     result->array[23] = param;
     return *result;
   };
   getBlockSignature(f);
   return x;
}

enum {
    BLOCK_HAS_COPY_DISPOSE =  (1 << 25),
    BLOCK_HAS_CXX_OBJ =       (1 << 26),
    BLOCK_IS_GLOBAL =         (1 << 28),
    BLOCK_USE_STRET =    (1 << 29),
    BLOCK_HAS_OBJC_TYPE  =    (1 << 30)
};

struct block_descriptor_big {
    unsigned long int reserved;
    unsigned long int size;
    void (*copy)(void *dst, void *src); // conditional on BLOCK_HAS_COPY_DISPOSE
    void (*dispose)(void *);            // conditional on BLOCK_HAS_COPY_DISPOSE
    const char *signature;                  // conditional on BLOCK_HAS_OBJC
    const char *layout;                 // conditional on BLOCK_HAS_OBJC
};
struct block_descriptor_small {
    unsigned long int reserved;
    unsigned long int size;
    const char *signature;              // conditional on BLOCK_HAS_OBJC
    const char *layout;                 // conditional on BLOCK_HAS_OBJC
};

struct block_layout_abi { // can't change
  void *isa;
  int flags;
  int reserved; 
  void (*invoke)(void *, ...);
  struct block_descriptor_big *descriptor;
};

const char *getBlockSignature(void *block) {
   struct block_layout_abi *layout = (struct block_layout_abi *)block;
   if ((layout->flags & BLOCK_HAS_OBJC_TYPE) != BLOCK_HAS_OBJC_TYPE) return 0;
   if (layout->flags & BLOCK_HAS_COPY_DISPOSE) 
      return layout->descriptor->signature;
   else
      return ((struct block_descriptor_small *)layout->descriptor)->signature;
}

int usesStruct(void *block) {
   struct block_layout_abi *layout = (struct block_layout_abi *)block;
   int want = BLOCK_HAS_OBJC_TYPE | BLOCK_USE_STRET;
   return (layout->flags & want) == want;
}
#endif

int main(int argc, char *argv[]) {
#if defined(__BLOCKS__) && defined(__clang__)
   if (!usesStruct(global))
     abort();
   BigStruct_t x;
   BigStruct_t (^local)(int) = ^(int param) {
     BigStruct_t *result = (BigStruct_t *)malloc(sizeof(BigStruct_t));
     result->array[23] = argc;
     return *result;
   };
   if (!usesStruct(global))
     abort();
   if (!usesStruct(local))
     abort();
   if (usesStruct(^void(int x){ }))
     abort();
#endif
   return 0;
}

/*
desired global flags: 1879048192
desired stack flags: 1610612736
should be non-zero: 1
should be non-zero: 1
should be non-zero: 1
should be zero: 0

*/
