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
   sl <<= cr;
   if(sl != 20){
     lrc = 301;
     if(prlc) printf(f,lrc);
   }
   sl = 5; sr = 2;
   sl <<= sr;
   if(sl != 20){
     lrc = 302;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ir = 2;
   sl <<= ir;
   if(sl != 20){
     lrc = 303;
     if(prlc) printf(f,lrc);
   }
   sl = 5; lr = 2;
   sl <<= lr;
   if(sl != 20){
     lrc = 304;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ur = 2;
   sl <<= ur;
   if(sl != 20){
     lrc = 305;
     if(prlc) printf(f,lrc);
   }
   il = 5; cr = 2;
   il <<= cr;
   if(il != 20){
     lrc = 306;
     if(prlc) printf(f,lrc);
   }
   il = 5; sr = 2;
   il <<= sr;
   if(il != 20){
     lrc = 307;
     if(prlc) printf(f,lrc);
   }
   il = 5; ir = 2;
   il <<= ir;
   if(il != 20){
     lrc = 308;
     if(prlc) printf(f,lrc);
   }
   il = 5; lr = 2;
   il <<= lr;
   if(il != 20){
     lrc = 309;
     if(prlc) printf(f,lrc);
   }
   il = 5; ur = 2;
   il <<= ur;
   if(il != 20){
     lrc = 310;
     if(prlc) printf(f,lrc);
   }
   ll = 5; cr = 2;
   ll <<= cr;
   if(ll != 20){
     lrc = 311;
     if(prlc) printf(f,lrc);
   }
   ll = 5; sr = 2;
   ll <<= sr;
   if(ll != 20){
     lrc = 312;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ir = 2;
   ll <<= ir;
   if(ll != 20){
     lrc = 313;
     if(prlc) printf(f,lrc);
   }
   ll = 5; lr = 2;
   ll <<= lr;
   if(ll != 20){
     lrc = 314;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ur = 2;
   ll <<= ur;
   if(ll != 20){
     lrc = 315;
     if(prlc) printf(f,lrc);
   }
   ul = 5; cr = 2;
   ul <<= cr;
   if(ul != 20){
     lrc = 316;
     if(prlc) printf(f,lrc);
   }
   ul = 5; sr = 2;
   ul <<= sr;
   if(ul != 20){
     lrc = 317;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ir = 2;
   ul <<= ir;
   if(ul != 20){
     lrc = 318;
     if(prlc) printf(f,lrc);
   }
   ul = 5; lr = 2;
   ul <<= lr;
   if(ul != 20){
     lrc = 319;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ur = 2;
   ul <<= ur;
   if(ul != 20){
     lrc = 320;
     if(prlc) printf(f,lrc);
   }
   cl = 12; cr = 10;
   cl &= cr;
   if(cl != 8){
     lrc = 321;
     if(prlc) printf(f,lrc);
   }
   cl = 12; sr = 10;
   cl &= sr;
   if(cl != 8){
     lrc = 322;
     if(prlc) printf(f,lrc);
   }
   cl = 12; ir = 10;
   cl &= ir;
   if(cl != 8){
     lrc = 323;
     if(prlc) printf(f,lrc);
   }
   cl = 12; lr = 10;
   cl &= lr;
   if(cl != 8){
     lrc = 324;
     if(prlc) printf(f,lrc);
   }
   cl = 12; ur = 10;
   cl &= ur;
   if(cl != 8){
     lrc = 325;
     if(prlc) printf(f,lrc);
   }
   sl = 12; cr = 10;
   sl &= cr;
   if(sl != 8){
     lrc = 326;
     if(prlc) printf(f,lrc);
   }
   sl = 12; sr = 10;
   sl &= sr;
   if(sl != 8){
     lrc = 327;
     if(prlc) printf(f,lrc);
   }
   sl = 12; ir = 10;
   sl &= ir;
   if(sl != 8){
     lrc = 328;
     if(prlc) printf(f,lrc);
   }
   sl = 12; lr = 10;
   sl &= lr;
   if(sl != 8){
     lrc = 329;
     if(prlc) printf(f,lrc);
   }
   sl = 12; ur = 10;
   sl &= ur;
   if(sl != 8){
     lrc = 330;
     if(prlc) printf(f,lrc);
   }
   il = 12; cr = 10;
   il &= cr;
   if(il != 8){
     lrc = 331;
     if(prlc) printf(f,lrc);
   }
   il = 12; sr = 10;
   il &= sr;
   if(il != 8){
     lrc = 332;
     if(prlc) printf(f,lrc);
   }
   il = 12; ir = 10;
   il &= ir;
   if(il != 8){
     lrc = 333;
     if(prlc) printf(f,lrc);
   }
   il = 12; lr = 10;
   il &= lr;
   if(il != 8){
     lrc = 334;
     if(prlc) printf(f,lrc);
   }
   il = 12; ur = 10;
   il &= ur;
   if(il != 8){
     lrc = 335;
     if(prlc) printf(f,lrc);
   }
   ll = 12; cr = 10;
   ll &= cr;
   if(ll != 8){
     lrc = 336;
     if(prlc) printf(f,lrc);
   }
   ll = 12; sr = 10;
   ll &= sr;
   if(ll != 8){
     lrc = 337;
     if(prlc) printf(f,lrc);
   }
   ll = 12; ir = 10;
   ll &= ir;
   if(ll != 8){
     lrc = 338;
     if(prlc) printf(f,lrc);
   }
   ll = 12; lr = 10;
   ll &= lr;
   if(ll != 8){
     lrc = 339;
     if(prlc) printf(f,lrc);
   }
   ll = 12; ur = 10;
   ll &= ur;
   if(ll != 8){
     lrc = 340;
     if(prlc) printf(f,lrc);
   }
   ul = 12; cr = 10;
   ul &= cr;
   if(ul != 8){
     lrc = 341;
     if(prlc) printf(f,lrc);
   }
   ul = 12; sr = 10;
   ul &= sr;
   if(ul != 8){
     lrc = 342;
     if(prlc) printf(f,lrc);
   }
   ul = 12; ir = 10;
   ul &= ir;
   if(ul != 8){
     lrc = 343;
     if(prlc) printf(f,lrc);
   }
   ul = 12; lr = 10;
   ul &= lr;
   if(ul != 8){
     lrc = 344;
     if(prlc) printf(f,lrc);
   }
   ul = 12; ur = 10;
   ul &= ur;
   if(ul != 8){
     lrc = 345;
     if(prlc) printf(f,lrc);
   }
   cl = 12; cr = 10;
   cl ^= cr;
   if(cl != 6){
     lrc = 346;
     if(prlc) printf(f,lrc);
   }
   cl = 12; sr = 10;
   cl ^= sr;
   if(cl != 6){
     lrc = 347;
     if(prlc) printf(f,lrc);
   }
   cl = 12; ir = 10;
   cl ^= ir;
   if(cl != 6){
     lrc = 348;
     if(prlc) printf(f,lrc);
   }
   cl = 12; lr = 10;
   cl ^= lr;
   if(cl != 6){
     lrc = 349;
     if(prlc) printf(f,lrc);
   }
   cl = 12; ur = 10;
   cl ^= ur;
   if(cl != 6){
     lrc = 350;
     if(prlc) printf(f,lrc);
   }
 

   if(lrc != 0) {
     rc = 1;
     if(pd0->flgd != 0) printf(s714er,1);
   }
   return rc;
}

#include "cq-main.h"
