#include "testharness.h"

int (*read_buf)(void *arg1, char *arg2, int arg3);

int file_read(void *gz1, char *buf, int size) {
    int total = 0, i;
    for (i=0;i<size;i++)
        total += buf[i];
    return total;
}

int main() {
    char mybuffer[5] = { 1, 2, 3, 4, 5}, sum = 0;
    void *foo = 0;

    read_buf = file_read;

    sum = read_buf(foo, mybuffer, 5);

    if (sum == 15) { SUCCESS; } 
    else { E(1); }
}
