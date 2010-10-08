   #include<stdio.h>
    #include<stdlib.h>
    #include<pString.c>
    #include<pString2.c>
    #include<pStrCpy.c>
    #include<pStrPrint.c>
    int main() {
      int * x = string();
      printf("%d;",x); strprint(x);
      int * y = string();
      printf("%d;",y); strprint(y);
      int * z = string2();
      printf("%d;",z); strprint(z);
      strCpy(x,z);
      printf("%d;", -1) ; strprint(x);
      printf("%d;", -1) ; strprint(y);
      printf("%d;", -1) ; strprint(z);
    }

