// PR671

#include <stdio.h>

int foo(long long v) {
    switch (v) {
    case 0:
        return 1;
    case -1:
        return 2;
    }
    return 0;
}

int main() {
    int r = foo(4294967295LL);
    printf("foo = %d\n", r);
    return r;
}
