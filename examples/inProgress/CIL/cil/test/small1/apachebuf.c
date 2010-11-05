#include <stdio.h>
#include "testharness.h"

unsigned short window[65536];

int set(char *buf, int value, int len) {
    int i;
    for (i=0;i<len;i++) buf[i] = value;
    return i;
}

int (*fun_ptr)(char *arg1, int arg2, int arg3);

int main() {

    set((char *) window, 1, 10); 

    /*
    if (* ((char *) window) != 1)
        E(1);
        */

    fun_ptr = set;

    fun_ptr((char *) window, 2, 10); 

    /*
    if (* ((char *) window) != 2)
        E(2);
        */

    SUCCESS;
}
