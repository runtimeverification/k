// attempt to reproduce this error:
//  Failure at ./Config_Test.mergedcured.c:open__112ACE_Malloc_T__tm__92_21ACE_Local_Memory_Pool29ACE_Local_Memory_Pool_Options16ACE_Thread_Mutex17ACE_Control_BlockFv_i:161967: Creating an unaligned sequence

#include <stdlib.h>

/* This code is from a custom allocator that allocates a header before the 
 * actual memory block */
int main() {
    struct header {
        int one;
        int *two;
        int three;
    } *h;
    char *p;
    // We allocate 3 chars but with a header
    char* v = (char*)malloc(sizeof(struct header) + 4);

#ifndef CCURED
    h = (struct header*)v; // Will check here that there is enough space in p
    h->one = 5; // Write something to the header
    p = (char*)(h + 1); // Skip the header, but this makes h SEQ
#else
    // In the CCURED version we have to play some tricks
    // Make sure h is not SEQ, so, don't do h + 1

    // We want h to be SAFE. If header did not contain pointers we could do:
    //                 h = (struct header*)v;
    // But since header contains pointers, it is not SAFE to cast from a
    // char-ptr to a header-ptr. trusted_cast wants its both ends to have
    // the same kind, which would make h SEQ. We use __ptrof instead.
    // But be careful how you use h in the future, because if you make it
    // SEQ, you will need __ptrof_qq, which does not exist!
    h = (struct header*)__ptrof(v);
    h->one = 5;
    // Use v to compute p, not h. This way h can stay SAFE.
    p = v + sizeof(struct header);
#endif
      
    // And we need the result to be SEQ
    p ++;
    p --;

    
    return 0;
}
