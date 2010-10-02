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

   sl = 12; cr = 10;
   sl ^= cr;
   if(sl != 6){
     lrc = 351;
     if(prlc) printf(f,lrc);
   }
   sl = 12; sr = 10;
   sl ^= sr;
   if(sl != 6){
     lrc = 352;
     if(prlc) printf(f,lrc);
   }
   sl = 12; ir = 10;
   sl ^= ir;
   if(sl != 6){
     lrc = 353;
     if(prlc) printf(f,lrc);
   }
   sl = 12; lr = 10;
   sl ^= lr;
   if(sl != 6){
     lrc = 354;
     if(prlc) printf(f,lrc);
   }
   sl = 12; ur = 10;
   sl ^= ur;
   if(sl != 6){
     lrc = 355;
     if(prlc) printf(f,lrc);
   }
   il = 12; cr = 10;
   il ^= cr;
   if(il != 6){
     lrc = 356;
     if(prlc) printf(f,lrc);
   }
   il = 12; sr = 10;
   il ^= sr;
   if(il != 6){
     lrc = 357;
     if(prlc) printf(f,lrc);
   }
   il = 12; ir = 10;
   il ^= ir;
   if(il != 6){
     lrc = 358;
     if(prlc) printf(f,lrc);
   }
   il = 12; lr = 10;
   il ^= lr;
   if(il != 6){
     lrc = 359;
     if(prlc) printf(f,lrc);
   }
   il = 12; ur = 10;
   il ^= ur;
   if(il != 6){
     lrc = 360;
     if(prlc) printf(f,lrc);
   }
   ll = 12; cr = 10;
   ll ^= cr;
   if(ll != 6){
     lrc = 361;
     if(prlc) printf(f,lrc);
   }
   ll = 12; sr = 10;
   ll ^= sr;
   if(ll != 6){
     lrc = 362;
     if(prlc) printf(f,lrc);
   }
   ll = 12; ir = 10;
   ll ^= ir;
   if(ll != 6){
     lrc = 363;
     if(prlc) printf(f,lrc);
   }
   ll = 12; lr = 10;
   ll ^= lr;
   if(ll != 6){
     lrc = 364;
     if(prlc) printf(f,lrc);
   }
   ll = 12; ur = 10;
   ll ^= ur;
   if(ll != 6){
     lrc = 365;
     if(prlc) printf(f,lrc);
   }
   ul = 12; cr = 10;
   ul ^= cr;
   if(ul != 6){
     lrc = 366;
     if(prlc) printf(f,lrc);
   }
   ul = 12; sr = 10;
   ul ^= sr;
   if(ul != 6){
     lrc = 367;
     if(prlc) printf(f,lrc);
   }
   ul = 12; ir = 10;
   ul ^= ir;
   if(ul != 6){
     lrc = 368;
     if(prlc) printf(f,lrc);
   }
   ul = 12; lr = 10;
   ul ^= lr;
   if(ul != 6){
     lrc = 369;
     if(prlc) printf(f,lrc);
   }
   ul = 12; ur = 10;
   ul ^= ur;
   if(ul != 6){
     lrc = 370;
     if(prlc) printf(f,lrc);
   }
   cl = 12; cr = 10;
   cl |= cr;
   if(cl != 14){
     lrc = 371;
     if(prlc) printf(f,lrc);
   }
   cl = 12; sr = 10;
   cl |= sr;
   if(cl != 14){
     lrc = 372;
     if(prlc) printf(f,lrc);
   }
   cl = 12; ir = 10;
   cl |= ir;
   if(cl != 14){
     lrc = 373;
     if(prlc) printf(f,lrc);
   }
   cl = 12; lr = 10;
   cl |= lr;
   if(cl != 14){
     lrc = 374;
     if(prlc) printf(f,lrc);
   }
   cl = 12; ur = 10;
   cl |= ur;
   if(cl != 14){
     lrc = 375;
     if(prlc) printf(f,lrc);
   }
   sl = 12; cr = 10;
   sl |= cr;
   if(sl != 14){
     lrc = 376;
     if(prlc) printf(f,lrc);
   }
   sl = 12; sr = 10;
   sl |= sr;
   if(sl != 14){
     lrc = 377;
     if(prlc) printf(f,lrc);
   }
   sl = 12; ir = 10;
   sl |= ir;
   if(sl != 14){
     lrc = 378;
     if(prlc) printf(f,lrc);
   }
   sl = 12; lr = 10;
   sl |= lr;
   if(sl != 14){
     lrc = 379;
     if(prlc) printf(f,lrc);
   }
   sl = 12; ur = 10;
   sl |= ur;
   if(sl != 14){
     lrc = 380;
     if(prlc) printf(f,lrc);
   }
   il = 12; cr = 10;
   il |= cr;
   if(il != 14){
     lrc = 381;
     if(prlc) printf(f,lrc);
   }
   il = 12; sr = 10;
   il |= sr;
   if(il != 14){
     lrc = 382;
     if(prlc) printf(f,lrc);
   }
   il = 12; ir = 10;
   il |= ir;
   if(il != 14){
     lrc = 383;
     if(prlc) printf(f,lrc);
   }
   il = 12; lr = 10;
   il |= lr;
   if(il != 14){
     lrc = 384;
     if(prlc) printf(f,lrc);
   }
   il = 12; ur = 10;
   il |= ur;
   if(il != 14){
     lrc = 385;
     if(prlc) printf(f,lrc);
   }
   ll = 12; cr = 10;
   ll |= cr;
   if(ll != 14){
     lrc = 386;
     if(prlc) printf(f,lrc);
   }
   ll = 12; sr = 10;
   ll |= sr;
   if(ll != 14){
     lrc = 387;
     if(prlc) printf(f,lrc);
   }
   ll = 12; ir = 10;
   ll |= ir;
   if(ll != 14){
     lrc = 388;
     if(prlc) printf(f,lrc);
   }
   ll = 12; lr = 10;
   ll |= lr;
   if(ll != 14){
     lrc = 389;
     if(prlc) printf(f,lrc);
   }
   ll = 12; ur = 10;
   ll |= ur;
   if(ll != 14){
     lrc = 390;
     if(prlc) printf(f,lrc);
   }
   ul = 12; cr = 10;
   ul |= cr;
   if(ul != 14){
     lrc = 391;
     if(prlc) printf(f,lrc);
   }
   ul = 12; sr = 10;
   ul |= sr;
   if(ul != 14){
     lrc = 392;
     if(prlc) printf(f,lrc);
   }
   ul = 12; ir = 10;
   ul |= ir;
   if(ul != 14){
     lrc = 393;
     if(prlc) printf(f,lrc);
   }
   ul = 12; lr = 10;
   ul |= lr;
   if(ul != 14){
     lrc = 394;
     if(prlc) printf(f,lrc);
   }
   ul = 12; ur = 10;
   ul |= ur;
   if(ul != 14){
     lrc = 395;
     if(prlc) printf(f,lrc);
   }
   
   if(lrc != 0) {
     rc = 1;
     if(pd0->flgd != 0) printf(s714er,1);
   }
   return rc;
}

#include "cq-main.h"
