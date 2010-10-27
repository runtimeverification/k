#include <stdio.h>
#include <stdlib.h>

union u {
        struct {
                unsigned int a : 8;
                unsigned int b : 3;
                unsigned int c : 3;
                unsigned int d : 3;
                unsigned int e : 3;
                unsigned int f : 3;
                unsigned int g : 3;
                unsigned int h : 3;
                unsigned int i : 3;

                unsigned int n : 8;
                unsigned int o : 8;
                unsigned int p : 8;
                unsigned int q : 8;
        } s;
        unsigned long long token;
};

int main(int argc, char *argv[])
{
        union u uu;
        uu.token = 0x012492490000FFFFULL;
        printf("p = 0x%02X\n", uu.s.p);
        return 0;
}

