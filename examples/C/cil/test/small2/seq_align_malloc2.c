// attempt to reproduce this error:
//  Failure at ./Config_Test.mergedcured.c:open__112ACE_Malloc_T__tm__92_21ACE_Local_Memory_Pool29ACE_Local_Memory_Pool_Options16ACE_Thread_Mutex17ACE_Control_BlockFv_i:161967: Creating an unaligned sequence

#include <stdio.h>
#include <stdlib.h>

struct a_struct {
    int one;
    int *two;
    int three;
};

#ifdef CCURED
  #define IFCCURED(cc,noncc) cc
#else
  #define IFCCURED(cc,noncc) noncc
#endif

#define CCURED_TRUSTED_CAST(t, what) \
        IFCCURED(((t)__trusted_cast((void*)(what))), ((t)(what)))

// imitate an allocator
void *make_a_struct(int num, size_t size) {
    // We allocate num things plus some extra.  Ccured hates this.
    return (struct a_struct *) malloc (num*size + 1);
}

int main() {
    const int array_size = 3;
    struct a_struct *p;

    char *temp = make_a_struct(array_size, sizeof *p);

#ifdef CCURED
    // Whack down the home area.
    temp = __align_seq(temp, sizeof *p);
#endif
    p = CCURED_TRUSTED_CAST(struct a_struct*, temp);
    // access it
    {
        int i;
        for(i=0; i<array_size; ++i) p[i].three = 17;
        for(i=0; i<array_size; ++i) {
            printf("p[%d].three = %d\n", i, p[i].three);
        }
    }
      
    // Force p to be SEQ
    p ++;
    p --;

    
    return 0;
}
