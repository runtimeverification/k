#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "pdefs.h"
#include "pcvt.h"
#include "precision.h"

/*
 * Output a string to a file.
 *
 * Returns:
 *   the number of characters written
 *   or EOF if error
 */
static int fouts(stream, chp)
   FILE *stream;
   register char *chp;
{
   register int count = 0, res = 0;

   if (chp != (char *) 0 && *chp != '\0')  do {
      count++;
      res = putc(*chp, stream);
   } while (*++chp != '\0' && res != EOF);

   if (res != EOF) res = count;
   return res;
}

/*
 * output the value of a precision to a file (no cr or whitespace)
 *
 * Returns:
 *    The number of characters output or EOF if error
 */
int fputp(stream, p)
   FILE *stream;
   precision p;
{
   int res;
   char *chp = ptoa(pparm(p));

   res = fouts(stream, chp);
   deallocate(chp);
   pdestroy(p);
   return res;
}

/*
 * Output a precision to stdout with a newline (useful from debugger)
 */
int putp(p)
   precision p;
{
   int res;
   char *chp = ptoa(pparm(p));

   res = fouts(stdout, chp);
   res = putc('\n', stdout);
   deallocate(chp);
   pdestroy(p);
   return res;
   
}

/*
 * Output a justified precision
 *
 * Returns: The number of characters in the precision, or EOF if error
 */
int fprintp(stream, p, minWidth)
   FILE *stream;
   precision p;
   register int minWidth;
{
   int res;
   char *chp = ptoa(pparm(p));
   int len;

   len = strlen(chp);
   if (minWidth < 0) {			/* left-justified */
      res = fouts(stream, chp);
      while (minWidth++ < -len) {
	 putc(' ', stream);
      }
   } else {
      while (minWidth-- > len) {	/* right-justified */
	 putc(' ', stream);
      }
      res = fouts(stream, chp);
   }

   deallocate(chp);
   pdestroy(p);
   return res;
}


/*
 * Read in a precision type - same as atop but with io
 * 
 *   leading whitespace skipped
 *   an optional leading '-' or '+' followed by digits '0'..'9' 
 *   leading 0's Ok
 *   stops at first unrecognized character
 *
 * Returns: pUndef if EOF or invalid argument (NULL or nondigit as 1st digit)
 */
precision fgetp(stream)
   FILE *stream;
{
   precision res   = pUndef;
   precision clump = pUndef;
   int sign = 0;
   register int ch;
   register accumulator temp, x; 
   register int j;

   ch = getc(stream);
   if (ch != EOF) {
      while (isspace(ch)) ch = getc(stream);	/* skip whitespace */
      if (ch == '-') {
	 sign = 1;
	 ch = getc(stream);
      } else if (ch == '+') {
	 ch = getc(stream);
      }
      if (isdigit(ch)) {
	 pset(&res, pzero);
	 pset(&clump, utop(aDigit));
	 do {
	    j = aDigitLog-1;
	    temp = ch - '0';
	    do {
	       if (!isdigit(ch = getc(stream))) goto atoplast;
	       temp = temp * aBase + (ch - '0');
	    } while (--j > 0);
	    pset(&res, padd(pmul(res, clump), utop(temp)));
	 } while (isdigit(ch = getc(stream)));
	 goto atopdone;
atoplast:
	 x = aBase;
	 while (j++ < aDigitLog-1) {
	    x *= aBase;
	 }
	 pset(&res, padd(pmul(res, utop(x)), utop(temp)));
atopdone:
	 if (ch != EOF) ungetc(ch, stream);
	 if (sign) {
	    pset(&res, pneg(res));
	 }
      } else {
	 if (ch == EOF) {
	    res = pUndef;
	 } else {
	    ungetc(ch, stream);
	 }
      }
   } else {
      res = pUndef;
   }
   pdestroy(clump);
   if (res == pUndef) return res;
   return presult(res);
}
