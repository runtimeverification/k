#include <stdio.h>

int main() {
    int x = 100 ,y = 200 ,z = 300, len = 6;

    char *p = "<<p>>" ,*q = "<<q>>" ,*r = "<<r>>" ;
    char dest_buf[1024];
    char *s1, *s2;

    printf("printf: %s %ld %0.20s %x\n",p,x,q,y);
    fprintf(stdout,"fprintf: %s %ld %0.20s %x\n",p,y,q,z);
    sprintf(dest_buf,"sprintf: %s %ld %0.20s %x",p,z,q,x);
    printf("printf: dest_buf = [%s]\n",dest_buf);

    s1 = &dest_buf[5];
    s2 = &s1[5];

    printf("printf: chop 5: [%s]\n", s1);
    printf("printf: chop 5 more, print %d: [%.*s]\n",len,len,s2);

    printf("printf: null = %s\n",(char*)0);

    return 0;
}
