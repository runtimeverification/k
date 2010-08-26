#include <stdio.h>

int main() {
    char const * p1 = "first string";
    const char * p2 = "second string";
    const int x = 5;
    const int y = 6;
    int const * p3 = &x;
    const int * p4 = &y;
    const double d = 5.5;

    printf("p1 = %s\n",p1);
    fprintf(stdout,"p2 = %s\n",p2); 
    printf("p3 = %p\n",(long)p3);
    fprintf(stdout,"p4 = %s\n",(long)p4); 
    printf("x = %d\n",x);
    printf("d = %g\n",d);

    return 0;
}
