#include "cq-header.h"

sec(pd0)                 /* 2.2 Identifiers (Names)      */
struct defs *pd0;
{
   int a234, a;
   int _, _234, A, rc;

   static char s22er[] = "s22,er%d\n";
   static char qs22[8] = "s22    ";

   char *ps, *pt;
                         /* Initialize                      */

   rc = 0;
   ps = qs22;
   pt = pd0 -> rfs;
   while (*pt++ = *ps++);

     /* An identifier is a sequence of letters and digits;
        the first character must be a letter. The under-
        score _ counts as a letter.                        */

   a=1;
   _=2;
   _234=3;
   a234=4;
   if(a+_+_234+a234 != 10) {
     rc = rc+1;
     if(pd0->flgd != 0) printf(s22er,1);
   }

   /* Upper and lower case letters are different.     */

   A = 2;
   if (A == a) {
     rc = rc+4;
     if (pd0->flgd != 0) printf(s22er,4);
   }

   return(rc);
}

#include "cq-main.h"
