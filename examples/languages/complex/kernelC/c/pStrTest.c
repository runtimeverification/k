    #include<stdio.h>
    #include<stdlib.h>
    #include<pString.c>
    #include<pStrCpy.c>
    #include<pStrLen.c>
    #include<pStrDup.c>
    #include<pStrPrint.c>
    int main() {
   int * x = string(); 
   int * y = strDup(x);
   strprint(y);
   free(x);
   free(y);
}

