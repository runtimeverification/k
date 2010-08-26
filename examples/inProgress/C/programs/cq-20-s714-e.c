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
   cl = 5; ur = 2;
   cl /= ur;
   if(cl != 2){
     lrc = 201;
     if(prlc) printf(f,lrc);
   }
   cl = 5; fr = 2;
   cl /= fr;
   if(cl != 2){
     lrc = 202;
     if(prlc) printf(f,lrc);
   }
   cl = 5; dr = 2;
   cl /= dr;
   if(cl != 2){
     lrc = 203;
     if(prlc) printf(f,lrc);
   }
   sl = 5; cr = 2;
   sl /= cr;
   if(sl != 2){
     lrc = 204;
     if(prlc) printf(f,lrc);
   }
   sl = 5; sr = 2;
   sl /= sr;
   if(sl != 2){
     lrc = 205;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ir = 2;
   sl /= ir;
   if(sl != 2){
     lrc = 206;
     if(prlc) printf(f,lrc);
   }
   sl = 5; lr = 2;
   sl /= lr;
   if(sl != 2){
     lrc = 207;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ur = 2;
   sl /= ur;
   if(sl != 2){
     lrc = 208;
     if(prlc) printf(f,lrc);
   }
   sl = 5; fr = 2;
   sl /= fr;
   if(sl != 2){
     lrc = 209;
     if(prlc) printf(f,lrc);
   }
   sl = 5; dr = 2;
   sl /= dr;
   if(sl != 2){
     lrc = 210;
     if(prlc) printf(f,lrc);
   }
   il = 5; cr = 2;
   il /= cr;
   if(il != 2){
     lrc = 211;
     if(prlc) printf(f,lrc);
   }
   il = 5; sr = 2;
   il /= sr;
   if(il != 2){
     lrc = 212;
     if(prlc) printf(f,lrc);
   }
   il = 5; ir = 2;
   il /= ir;
   if(il != 2){
     lrc = 213;
     if(prlc) printf(f,lrc);
   }
   il = 5; lr = 2;
   il /= lr;
   if(il != 2){
     lrc = 214;
     if(prlc) printf(f,lrc);
   }
   il = 5; ur = 2;
   il /= ur;
   if(il != 2){
     lrc = 215;
     if(prlc) printf(f,lrc);
   }
   il = 5; fr = 2;
   il /= fr;
   if(il != 2){
     lrc = 216;
     if(prlc) printf(f,lrc);
   }
   il = 5; dr = 2;
   il /= dr;
   if(il != 2){
     lrc = 217;
     if(prlc) printf(f,lrc);
   }
   ll = 5; cr = 2;
   ll /= cr;
   if(ll != 2){
     lrc = 218;
     if(prlc) printf(f,lrc);
   }
   ll = 5; sr = 2;
   ll /= sr;
   if(ll != 2){
     lrc = 219;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ir = 2;
   ll /= ir;
   if(ll != 2){
     lrc = 220;
     if(prlc) printf(f,lrc);
   }
   ll = 5; lr = 2;
   ll /= lr;
   if(ll != 2){
     lrc = 221;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ur = 2;
   ll /= ur;
   if(ll != 2){
     lrc = 222;
     if(prlc) printf(f,lrc);
   }
   ll = 5; fr = 2;
   ll /= fr;
   if(ll != 2){
     lrc = 223;
     if(prlc) printf(f,lrc);
   }
   ll = 5; dr = 2;
   ll /= dr;
   if(ll != 2){
     lrc = 224;
     if(prlc) printf(f,lrc);
   }
   ul = 5; cr = 2;
   ul /= cr;
   if(ul != 2){
     lrc = 225;
     if(prlc) printf(f,lrc);
   }
   ul = 5; sr = 2;
   ul /= sr;
   if(ul != 2){
     lrc = 226;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ir = 2;
   ul /= ir;
   if(ul != 2){
     lrc = 227;
     if(prlc) printf(f,lrc);
   }
   ul = 5; lr = 2;
   ul /= lr;
   if(ul != 2){
     lrc = 228;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ur = 2;
   ul /= ur;
   if(ul != 2){
     lrc = 229;
     if(prlc) printf(f,lrc);
   }
   ul = 5; fr = 2;
   ul /= fr;
   if(ul != 2){
     lrc = 230;
     if(prlc) printf(f,lrc);
   }
   ul = 5; dr = 2;
   ul /= dr;
   if(ul != 2){
     lrc = 231;
     if(prlc) printf(f,lrc);
   }
   fl = 5; cr = 2;
   fl /= cr;
   if(fl != 2.5){
     lrc = 232;
     if(prlc) printf(f,lrc);
   }
   fl = 5; sr = 2;
   fl /= sr;
   if(fl != 2.5){
     lrc = 233;
     if(prlc) printf(f,lrc);
   }
   fl = 5; ir = 2;
   fl /= ir;
   if(fl != 2.5){
     lrc = 234;
     if(prlc) printf(f,lrc);
   }
   fl = 5; lr = 2;
   fl /= lr;
   if(fl != 2.5){
     lrc = 235;
     if(prlc) printf(f,lrc);
   }
   fl = 5; ur = 2;
   fl /= ur;
   if(fl != 2.5){
     lrc = 236;
     if(prlc) printf(f,lrc);
   }
   fl = 5; fr = 2;
   fl /= fr;
   if(fl != 2.5){
     lrc = 237;
     if(prlc) printf(f,lrc);
   }
   fl = 5; dr = 2;
   fl /= dr;
   if(fl != 2.5){
     lrc = 238;
     if(prlc) printf(f,lrc);
   }
   dl = 5; cr = 2;
   dl /= cr;
   if(dl != 2.5){
     lrc = 239;
     if(prlc) printf(f,lrc);
   }
   dl = 5; sr = 2;
   dl /= sr;
   if(dl != 2.5){
     lrc = 240;
     if(prlc) printf(f,lrc);
   }
   dl = 5; ir = 2;
   dl /= ir;
   if(dl != 2.5){
     lrc = 241;
     if(prlc) printf(f,lrc);
   }
   dl = 5; lr = 2;
   dl /= lr;
   if(dl != 2.5){
     lrc = 242;
     if(prlc) printf(f,lrc);
   }
   dl = 5; ur = 2;
   dl /= ur;
   if(dl != 2.5){
     lrc = 243;
     if(prlc) printf(f,lrc);
   }
   dl = 5; fr = 2;
   dl /= fr;
   if(dl != 2.5){
     lrc = 244;
     if(prlc) printf(f,lrc);
   }
   dl = 5; dr = 2;
   dl /= dr;
   if(dl != 2.5){
     lrc = 245;
     if(prlc) printf(f,lrc);
   }
   cl = 5; cr = 2;
   cl %= cr;
   if(cl != 1){
     lrc = 246;
     if(prlc) printf(f,lrc);
   }
   cl = 5; sr = 2;
   cl %= sr;
   if(cl != 1){
     lrc = 247;
     if(prlc) printf(f,lrc);
   }
   cl = 5; ir = 2;
   cl %= ir;
   if(cl != 1){
     lrc = 248;
     if(prlc) printf(f,lrc);
   }
   cl = 5; lr = 2;
   cl %= lr;
   if(cl != 1){
     lrc = 249;
     if(prlc) printf(f,lrc);
   }
   cl = 5; ur = 2;
   cl %= ur;
   if(cl != 1){
     lrc = 250;
     if(prlc) printf(f,lrc);
   }



   if(lrc != 0) {
     rc = 1;
     if(pd0->flgd != 0) printf(s714er,1);
   }
   return rc;
}

#include "cq-main.h"
