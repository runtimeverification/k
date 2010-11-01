#include "cq-header.h"


sec(pd0)          /*  7.14  Assignment operators       */
struct defs *pd0;
{
   static char f[] = "Local error %d.\n";
   static char s714er[] = "s714,er%d\n";
   static char qs714[8] = "s714   ";
   register int prlc, lrc;
   int rc;
   char cl, cr;
   short sl, sr;
   int il, ir;
   long ll, lr;
   unsigned ul, ur;
   float fl, fr;
   double dl, dr;
   char *ps, *pt;
   ps = qs714;
   pt = pd0->rfs;
   rc = 0;
   lrc = 0;
   prlc = pd0->flgl;
   while (*pt++ = *ps++);

        /* This section tests the assignment operators.

        It is an exhaustive test of all assignment statements
        of the form:

                vl op vr

        where vl and vr are variables from the set
        {char,short,int,long,unsigned,float,double} and op is
        one of the assignment operators. There are 395 such
        statements.

        The initial values for the variables have been chosen
        so that both the initial values and the results will
        "fit" in just about any implementation, and that the re-
        sults will be such that they test for the proper form-
        ation of composite operators, rather than checking for
        the valid operation of those operators' components.
        For example, in checking >>=, we want to verify that
        a right shift and a move take place, rather than
        whether or not there may be some peculiarities about
        the right shift. Such tests have been made previously,
        and to repeat them here would be to throw out a red
        herring.

        The table below lists the operators, assignment targets,
        initial values for left and right operands, and the
        expected values of the results.


          =  +=  -=  *=  /=  %=  >>=  <<=  &=  ^=  |=	
char      2   7   3  10   2   1   1    20   8   6  14
short     2   7   3  10   2   1   1    20   8   6  14
int       2   7   3  10   2   1   1    20   8   6  14
long      2   7   3  10   2   1   1    20   8   6  14
unsigned  2   7   3  10   2   1   1    20   8   6  14
float     2   7   3  10 2.5 |             |
double    2   7   3  10 2.5 |             |
                            |             |
initial         (5,2)       |    (5,2)    |  (12,10)

        The following machine-generated program reflects the
        tests described in the table.
                                                                */

   sl = 5; cr = 2;
   sl %= cr;
   if(sl != 1){
     lrc = 251;
     if(prlc) printf(f,lrc);
   }
   sl = 5; sr = 2;
   sl %= sr;
   if(sl != 1){
     lrc = 252;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ir = 2;
   sl %= ir;
   if(sl != 1){
     lrc = 253;
     if(prlc) printf(f,lrc);
   }
   sl = 5; lr = 2;
   sl %= lr;
   if(sl != 1){
     lrc = 254;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ur = 2;
   sl %= ur;
   if(sl != 1){
     lrc = 255;
     if(prlc) printf(f,lrc);
   }
   il = 5; cr = 2;
   il %= cr;
   if(il != 1){
     lrc = 256;
     if(prlc) printf(f,lrc);
   }
   il = 5; sr = 2;
   il %= sr;
   if(il != 1){
     lrc = 257;
     if(prlc) printf(f,lrc);
   }
   il = 5; ir = 2;
   il %= ir;
   if(il != 1){
     lrc = 258;
     if(prlc) printf(f,lrc);
   }
   il = 5; lr = 2;
   il %= lr;
   if(il != 1){
     lrc = 259;
     if(prlc) printf(f,lrc);
   }
   il = 5; ur = 2;
   il %= ur;
   if(il != 1){
     lrc = 260;
     if(prlc) printf(f,lrc);
   }
   ll = 5; cr = 2;
   ll %= cr;
   if(ll != 1){
     lrc = 261;
     if(prlc) printf(f,lrc);
   }
   ll = 5; sr = 2;
   ll %= sr;
   if(ll != 1){
     lrc = 262;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ir = 2;
   ll %= ir;
   if(ll != 1){
     lrc = 263;
     if(prlc) printf(f,lrc);
   }
   ll = 5; lr = 2;
   ll %= lr;
   if(ll != 1){
     lrc = 264;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ur = 2;
   ll %= ur;
   if(ll != 1){
     lrc = 265;
     if(prlc) printf(f,lrc);
   }
   ul = 5; cr = 2;
   ul %= cr;
   if(ul != 1){
     lrc = 266;
     if(prlc) printf(f,lrc);
   }
   ul = 5; sr = 2;
   ul %= sr;
   if(ul != 1){
     lrc = 267;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ir = 2;
   ul %= ir;
   if(ul != 1){
     lrc = 268;
     if(prlc) printf(f,lrc);
   }
   ul = 5; lr = 2;
   ul %= lr;
   if(ul != 1){
     lrc = 269;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ur = 2;
   ul %= ur;
   if(ul != 1){
     lrc = 270;
     if(prlc) printf(f,lrc);
   }
   cl = 5; cr = 2;
   cl >>= cr;
   if(cl != 1){
     lrc = 271;
     if(prlc) printf(f,lrc);
   }
   cl = 5; sr = 2;
   cl >>= sr;
   if(cl != 1){
     lrc = 272;
     if(prlc) printf(f,lrc);
   }
   cl = 5; ir = 2;
   cl >>= ir;
   if(cl != 1){
     lrc = 273;
     if(prlc) printf(f,lrc);
   }
   cl = 5; lr = 2;
   cl >>= lr;
   if(cl != 1){
     lrc = 274;
     if(prlc) printf(f,lrc);
   }
   cl = 5; ur = 2;
   cl >>= ur;
   if(cl != 1){
     lrc = 275;
     if(prlc) printf(f,lrc);
   }
   sl = 5; cr = 2;
   sl >>= cr;
   if(sl != 1){
     lrc = 276;
     if(prlc) printf(f,lrc);
   }
   sl = 5; sr = 2;
   sl >>= sr;
   if(sl != 1){
     lrc = 277;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ir = 2;
   sl >>= ir;
   if(sl != 1){
     lrc = 278;
     if(prlc) printf(f,lrc);
   }
   sl = 5; lr = 2;
   sl >>= lr;
   if(sl != 1){
     lrc = 279;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ur = 2;
   sl >>= ur;
   if(sl != 1){
     lrc = 280;
     if(prlc) printf(f,lrc);
   }
   il = 5; cr = 2;
   il >>= cr;
   if(il != 1){
     lrc = 281;
     if(prlc) printf(f,lrc);
   }
   il = 5; sr = 2;
   il >>= sr;
   if(il != 1){
     lrc = 282;
     if(prlc) printf(f,lrc);
   }
   il = 5; ir = 2;
   il >>= ir;
   if(il != 1){
     lrc = 283;
     if(prlc) printf(f,lrc);
   }
   il = 5; lr = 2;
   il >>= lr;
   if(il != 1){
     lrc = 284;
     if(prlc) printf(f,lrc);
   }
   il = 5; ur = 2;
   il >>= ur;
   if(il != 1){
     lrc = 285;
     if(prlc) printf(f,lrc);
   }
   ll = 5; cr = 2;
   ll >>= cr;
   if(ll != 1){
     lrc = 286;
     if(prlc) printf(f,lrc);
   }
   ll = 5; sr = 2;
   ll >>= sr;
   if(ll != 1){
     lrc = 287;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ir = 2;
   ll >>= ir;
   if(ll != 1){
     lrc = 288;
     if(prlc) printf(f,lrc);
   }
   ll = 5; lr = 2;
   ll >>= lr;
   if(ll != 1){
     lrc = 289;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ur = 2;
   ll >>= ur;
   if(ll != 1){
     lrc = 290;
     if(prlc) printf(f,lrc);
   }
   ul = 5; cr = 2;
   ul >>= cr;
   if(ul != 1){
     lrc = 291;
     if(prlc) printf(f,lrc);
   }
   ul = 5; sr = 2;
   ul >>= sr;
   if(ul != 1){
     lrc = 292;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ir = 2;
   ul >>= ir;
   if(ul != 1){
     lrc = 293;
     if(prlc) printf(f,lrc);
   }
   ul = 5; lr = 2;
   ul >>= lr;
   if(ul != 1){
     lrc = 294;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ur = 2;
   ul >>= ur;
   if(ul != 1){
     lrc = 295;
     if(prlc) printf(f,lrc);
   }
   cl = 5; cr = 2;
   cl <<= cr;
   if(cl != 20){
     lrc = 296;
     if(prlc) printf(f,lrc);
   }
   cl = 5; sr = 2;
   cl <<= sr;
   if(cl != 20){
     lrc = 297;
     if(prlc) printf(f,lrc);
   }
   cl = 5; ir = 2;
   cl <<= ir;
   if(cl != 20){
     lrc = 298;
     if(prlc) printf(f,lrc);
   }
   cl = 5; lr = 2;
   cl <<= lr;
   if(cl != 20){
     lrc = 299;
     if(prlc) printf(f,lrc);
   }
   cl = 5; ur = 2;
   cl <<= ur;
   if(cl != 20){
     lrc = 300;
     if(prlc) printf(f,lrc);
   }

   
   
   if(lrc != 0) {
     rc = 1;
     if(pd0->flgd != 0) printf(s714er,1);
   }
   return rc;
}


#include "cq-main.h"