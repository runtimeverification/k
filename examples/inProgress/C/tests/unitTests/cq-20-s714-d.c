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

   cl = 5; lr = 2;
   cl *= lr;
   if(cl != 10){
     lrc = 151;
     if(prlc) printf(f,lrc);
   }
   cl = 5; ur = 2;
   cl *= ur;
   if(cl != 10){
     lrc = 152;
     if(prlc) printf(f,lrc);
   }
   cl = 5; fr = 2;
   cl *= fr;
   if(cl != 10){
     lrc = 153;
     if(prlc) printf(f,lrc);
   }
   cl = 5; dr = 2;
   cl *= dr;
   if(cl != 10){
     lrc = 154;
     if(prlc) printf(f,lrc);
   }
   sl = 5; cr = 2;
   sl *= cr;
   if(sl != 10){
     lrc = 155;
     if(prlc) printf(f,lrc);
   }
   sl = 5; sr = 2;
   sl *= sr;
   if(sl != 10){
     lrc = 156;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ir = 2;
   sl *= ir;
   if(sl != 10){
     lrc = 157;
     if(prlc) printf(f,lrc);
   }
   sl = 5; lr = 2;
   sl *= lr;
   if(sl != 10){
     lrc = 158;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ur = 2;
   sl *= ur;
   if(sl != 10){
     lrc = 159;
     if(prlc) printf(f,lrc);
   }
   sl = 5; fr = 2;
   sl *= fr;
   if(sl != 10){
     lrc = 160;
     if(prlc) printf(f,lrc);
   }
   sl = 5; dr = 2;
   sl *= dr;
   if(sl != 10){
     lrc = 161;
     if(prlc) printf(f,lrc);
   }
   il = 5; cr = 2;
   il *= cr;
   if(il != 10){
     lrc = 162;
     if(prlc) printf(f,lrc);
   }
   il = 5; sr = 2;
   il *= sr;
   if(il != 10){
     lrc = 163;
     if(prlc) printf(f,lrc);
   }
   il = 5; ir = 2;
   il *= ir;
   if(il != 10){
     lrc = 164;
     if(prlc) printf(f,lrc);
   }
   il = 5; lr = 2;
   il *= lr;
   if(il != 10){
     lrc = 165;
     if(prlc) printf(f,lrc);
   }
   il = 5; ur = 2;
   il *= ur;
   if(il != 10){
     lrc = 166;
     if(prlc) printf(f,lrc);
   }
   il = 5; fr = 2;
   il *= fr;
   if(il != 10){
     lrc = 167;
     if(prlc) printf(f,lrc);
   }
   il = 5; dr = 2;
   il *= dr;
   if(il != 10){
     lrc = 168;
     if(prlc) printf(f,lrc);
   }
   ll = 5; cr = 2;
   ll *= cr;
   if(ll != 10){
     lrc = 169;
     if(prlc) printf(f,lrc);
   }
   ll = 5; sr = 2;
   ll *= sr;
   if(ll != 10){
     lrc = 170;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ir = 2;
   ll *= ir;
   if(ll != 10){
     lrc = 171;
     if(prlc) printf(f,lrc);
   }
   ll = 5; lr = 2;
   ll *= lr;
   if(ll != 10){
     lrc = 172;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ur = 2;
   ll *= ur;
   if(ll != 10){
     lrc = 173;
     if(prlc) printf(f,lrc);
   }
   ll = 5; fr = 2;
   ll *= fr;
   if(ll != 10){
     lrc = 174;
     if(prlc) printf(f,lrc);
   }
   ll = 5; dr = 2;
   ll *= dr;
   if(ll != 10){
     lrc = 175;
     if(prlc) printf(f,lrc);
   }
   ul = 5; cr = 2;
   ul *= cr;
   if(ul != 10){
     lrc = 176;
     if(prlc) printf(f,lrc);
   }
   ul = 5; sr = 2;
   ul *= sr;
   if(ul != 10){
     lrc = 177;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ir = 2;
   ul *= ir;
   if(ul != 10){
     lrc = 178;
     if(prlc) printf(f,lrc);
   }
   ul = 5; lr = 2;
   ul *= lr;
   if(ul != 10){
     lrc = 179;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ur = 2;
   ul *= ur;
   if(ul != 10){
     lrc = 180;
     if(prlc) printf(f,lrc);
   }
   ul = 5; fr = 2;
   ul *= fr;
   if(ul != 10){
     lrc = 181;
     if(prlc) printf(f,lrc);
   }
   ul = 5; dr = 2;
   ul *= dr;
   if(ul != 10){
     lrc = 182;
     if(prlc) printf(f,lrc);
   }
   fl = 5; cr = 2;
   fl *= cr;
   if(fl != 10){
     lrc = 183;
     if(prlc) printf(f,lrc);
   }
   fl = 5; sr = 2;
   fl *= sr;
   if(fl != 10){
     lrc = 184;
     if(prlc) printf(f,lrc);
   }
   fl = 5; ir = 2;
   fl *= ir;
   if(fl != 10){
     lrc = 185;
     if(prlc) printf(f,lrc);
   }
   fl = 5; lr = 2;
   fl *= lr;
   if(fl != 10){
     lrc = 186;
     if(prlc) printf(f,lrc);
   }
   fl = 5; ur = 2;
   fl *= ur;
   if(fl != 10){
     lrc = 187;
     if(prlc) printf(f,lrc);
   }
   fl = 5; fr = 2;
   fl *= fr;
   if(fl != 10){
     lrc = 188;
     if(prlc) printf(f,lrc);
   }
   fl = 5; dr = 2;
   fl *= dr;
   if(fl != 10){
     lrc = 189;
     if(prlc) printf(f,lrc);
   }
   dl = 5; cr = 2;
   dl *= cr;
   if(dl != 10){
     lrc = 190;
     if(prlc) printf(f,lrc);
   }
   dl = 5; sr = 2;
   dl *= sr;
   if(dl != 10){
     lrc = 191;
     if(prlc) printf(f,lrc);
   }
   dl = 5; ir = 2;
   dl *= ir;
   if(dl != 10){
     lrc = 192;
     if(prlc) printf(f,lrc);
   }
   dl = 5; lr = 2;
   dl *= lr;
   if(dl != 10){
     lrc = 193;
     if(prlc) printf(f,lrc);
   }
   dl = 5; ur = 2;
   dl *= ur;
   if(dl != 10){
     lrc = 194;
     if(prlc) printf(f,lrc);
   }
   dl = 5; fr = 2;
   dl *= fr;
   if(dl != 10){
     lrc = 195;
     if(prlc) printf(f,lrc);
   }
   dl = 5; dr = 2;
   dl *= dr;
   if(dl != 10){
     lrc = 196;
     if(prlc) printf(f,lrc);
   }
   cl = 5; cr = 2;
   cl /= cr;
   if(cl != 2){
     lrc = 197;
     if(prlc) printf(f,lrc);
   }
   cl = 5; sr = 2;
   cl /= sr;
   if(cl != 2){
     lrc = 198;
     if(prlc) printf(f,lrc);
   }
   cl = 5; ir = 2;
   cl /= ir;
   if(cl != 2){
     lrc = 199;
     if(prlc) printf(f,lrc);
   }
   cl = 5; lr = 2;
   cl /= lr;
   if(cl != 2){
     lrc = 200;
     if(prlc) printf(f,lrc);
   }
    
   if(lrc != 0) {
     rc = 1;
     if(pd0->flgd != 0) printf(s714er,1);
   }
   return rc;
}

#include "cq-main.h"
