#include <string.h>
#include <stdio.h>

int main () {
   int i;
   char a[]="CCu";
   char b[3];

   strcpy (b,a);

   for (i=0; i<4; i++)
     printf ("b[%d] = %c (%d)\n", i, b[i], b[i]);

}
