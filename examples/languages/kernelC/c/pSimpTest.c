 #include<stdio.h>
    #include<stdlib.h>
    int main() {
     int * x = (int *)malloc(3*sizeof(int));
     if (x == NULL) printf("%d;",-1); else printf("%d;",x);
} 

