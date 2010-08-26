#include "cq-header.h"

int sec(pd0)          /* Characters and integers */
struct defs *pd0;
{
   static char s61er[] = "s61,er%d\n";
   static char qs61[8] = "s61    ";
   short from, shortint;
   long int to, longint;
   int rc, lrc;
   int j;
   char fromc, charint;
   char *wd, *pc[6];
   
   static char upper_alpha[]             = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
   static char lower_alpha[]             = "abcdefghijklmnopqrstuvwxyz";
   static char numbers[]               = "0123456789";
   static char special_characters[]    = "~!\"#%&()_=-^|{}[]+;*:<>,.?/";
   static char extra_special_characters[] = "\n\t\b\r\f\\\'";
   static char blank_and_NUL[]            = " \0";

   char *ps, *pt;
   ps = qs61;
   pt = pd0->rfs;
   rc = 0;
   while (*pt++ = *ps++);

/*      A character or a short integer may be used wherever
an integer may be used. In all cases, the value is converted
to integer. This principle is extensively used throughout this
program, and will not be explicitly tested here.        */

/*      Conversion of a shorter integer to a longer always
involves sign extension.                                */

   from = -19;
   to = from;

   if(to != -19){
     rc = rc+1;
     if(pd0->flgd != 0) printf(s61er,1);
   }

/*      It is guaranteed that a member of the standard char-
acter set is nonnegative.                               */

   pc[0] = upper_alpha;
   pc[1] = lower_alpha;
   pc[2] = numbers;
   pc[3] = special_characters;
   pc[4] = extra_special_characters;
   pc[5] = blank_and_NUL;

   lrc = 0;
   for (j=0; j<6; j++)
     while(*pc[j]) if(*pc[j]++ < 0) lrc =1;

   if(lrc != 0){
     rc=rc+2;
     if(pd0->flgd != 0) printf(s61er,2);
   }

/*      When a longer integer is converted to a shorter or
to  a char, it is truncated on the left; excess bits are 
simply discarded.                                       */

   longint = 1048579;           /* =2**20+3 */
   shortint = longint;
   charint = longint;
   // cme :(
	int guard = (shortint != longint && shortint != 3);
	if (!guard) {
		guard = (charint  != longint && charint  != 3);
	}
   if(guard) {
     rc = rc+8;
     if(pd0->flgd != 0) printf(s61er,8);
   }

   return rc;
}
#include "cq-main.h"
