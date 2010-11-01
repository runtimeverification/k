#include "cq-header.h"

int sec(pd0)                   /*  2.4.3 Character constants  */
struct defs *pd0;
{
   static char s243er[] = "s243,er%d\n";
   static char qs243[8] = "s243   ";
   char *ps, *pt;
   int rc;
   char chars[256];

   rc = 0;
   ps = qs243;
   pt = pd0->rfs;
   while(*pt++ = *ps++);

     /* One of the problems that arises when testing character constants
        is that of definition: What, exactly, is the character set?
        In order to guarantee a certain amount of machine independence,
        the character set we will use here is the set of characters writ-
        able as escape sequences in C, plus those characters used in writ-
        ing C programs, i.e.,

        letters:
                   ABCDEFGHIJKLMNOPQRSTUVWXYZ      26
                   abcdefghijklmnopqrstuvwxyz      26
        numbers:
                   0123456789                      10
        special characters:
                   ~!"#%&()_=-^|{}[]+;*:<>,.?/     27
        extra special characters:
                   newline           \n       
                   horizontal tab    \t
                   backspace         \b
                   carriage return   \r
                   form feed         \f
                   backslash         \\
                   single quote      \'             7
        blank & NUL                                 2
                                                  ---
                                                   98

        Any specific implementation of C may of course support additional
        characters.                                       */

        /* Since the value of a character constant is the numerical value
           of the character in the machine's character set, there should
           be a one-to-one correspondence between characters and values. */

   zerofill(chars);

   chars['a'] = 1;   chars['A'] = 1;   chars['~'] = 1;   chars['0'] = 1;
   chars['b'] = 1;   chars['B'] = 1;   chars['!'] = 1;   chars['1'] = 1;
   chars['c'] = 1;   chars['C'] = 1;   chars['"'] = 1;   chars['2'] = 1;
   chars['d'] = 1;   chars['D'] = 1;   chars['#'] = 1;   chars['3'] = 1;
   chars['e'] = 1;   chars['E'] = 1;   chars['%'] = 1;   chars['4'] = 1;
   chars['f'] = 1;   chars['F'] = 1;   chars['&'] = 1;   chars['5'] = 1;
   chars['g'] = 1;   chars['G'] = 1;   chars['('] = 1;   chars['6'] = 1;
   chars['h'] = 1;   chars['H'] = 1;   chars[')'] = 1;   chars['7'] = 1;
   chars['i'] = 1;   chars['I'] = 1;   chars['_'] = 1;   chars['8'] = 1;
   chars['j'] = 1;   chars['J'] = 1;   chars['='] = 1;   chars['9'] = 1;
   chars['k'] = 1;   chars['K'] = 1;   chars['-'] = 1;
   chars['l'] = 1;   chars['L'] = 1;   chars['^'] = 1;
   chars['m'] = 1;   chars['M'] = 1;   chars['|'] = 1;   chars['\n'] = 1;
   chars['n'] = 1;   chars['N'] = 1;                     chars['\t'] = 1;
   chars['o'] = 1;   chars['O'] = 1;   chars['{'] = 1;   chars['\b'] = 1;
   chars['p'] = 1;   chars['P'] = 1;   chars['}'] = 1;   chars['\r'] = 1;
   chars['q'] = 1;   chars['Q'] = 1;   chars['['] = 1;   chars['\f'] = 1;
   chars['r'] = 1;   chars['R'] = 1;   chars[']'] = 1;
   chars['s'] = 1;   chars['S'] = 1;   chars['+'] = 1;   chars['\\'] = 1;
   chars['t'] = 1;   chars['T'] = 1;   chars[';'] = 1;   chars['\''] = 1;
   chars['u'] = 1;   chars['U'] = 1;   chars['*'] = 1;  
   chars['v'] = 1;   chars['V'] = 1;   chars[':'] = 1;   chars['\0'] = 1;
   chars['w'] = 1;   chars['W'] = 1;   chars['<'] = 1;   chars[' '] = 1;
   chars['x'] = 1;   chars['X'] = 1;   chars['>'] = 1;
   chars['y'] = 1;   chars['Y'] = 1;   chars[','] = 1;
   chars['z'] = 1;   chars['Z'] = 1;   chars['.'] = 1;
                                       chars['?'] = 1;
                                       chars['/'] = 1;

   if(sumof(chars) != 98){
     rc = rc+1;
     if(pd0->flgd != 0) printf(s243er,1);
   }

   /* Finally, the escape \ddd consists of the backslash followed
      by 1, 2, or 3 octal digits which are taken to specify  the
      desired character.                           */

   if( '\0'    !=   0 || '\01'   !=   1 || '\02'   !=   2
    || '\03'   !=   3 || '\04'   !=   4 || '\05'   !=   5
    || '\06'   !=   6 || '\07'   !=   7 || '\10'   !=   8
    || '\17'   !=  15 || '\20'   !=  16 || '\77'   !=  63
    || '\100'  !=  64 || '\177'  != 127                 ){
   
     rc = rc+8;
     if(pd0->flgd != 0) printf(s243er,8);
   }

   return rc;
}

#include "cq-main.h"
