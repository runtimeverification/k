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

   cl = 5; sr = 2;
   cl += sr;
   if(cl != 7){
     lrc = 51;
     if(prlc) printf(f,lrc);
   }
   cl = 5; ir = 2;
   cl += ir;
   if(cl != 7){
     lrc = 52;
     if(prlc) printf(f,lrc);
   }
   cl = 5; lr = 2;
   cl += lr;
   if(cl != 7){
     lrc = 53;
     if(prlc) printf(f,lrc);
   }
   cl = 5; ur = 2;
   cl += ur;
   if(cl != 7){
     lrc = 54;
     if(prlc) printf(f,lrc);
   }
   cl = 5; fr = 2;
   cl += fr;
   if(cl != 7){
     lrc = 55;
     if(prlc) printf(f,lrc);
   }
   cl = 5; dr = 2;
   cl += dr;
   if(cl != 7){
     lrc = 56;
     if(prlc) printf(f,lrc);
   }
   sl = 5; cr = 2;
   sl += cr;
   if(sl != 7){
     lrc = 57;
     if(prlc) printf(f,lrc);
   }
   sl = 5; sr = 2;
   sl += sr;
   if(sl != 7){
     lrc = 58;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ir = 2;
   sl += ir;
   if(sl != 7){
     lrc = 59;
     if(prlc) printf(f,lrc);
   }
   sl = 5; lr = 2;
   sl += lr;
   if(sl != 7){
     lrc = 60;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ur = 2;
   sl += ur;
   if(sl != 7){
     lrc = 61;
     if(prlc) printf(f,lrc);
   }
   sl = 5; fr = 2;
   sl += fr;
   if(sl != 7){
     lrc = 62;
     if(prlc) printf(f,lrc);
   }
   sl = 5; dr = 2;
   sl += dr;
   if(sl != 7){
     lrc = 63;
     if(prlc) printf(f,lrc);
   }
   il = 5; cr = 2;
   il += cr;
   if(il != 7){
     lrc = 64;
     if(prlc) printf(f,lrc);
   }
   il = 5; sr = 2;
   il += sr;
   if(il != 7){
     lrc = 65;
     if(prlc) printf(f,lrc);
   }
   il = 5; ir = 2;
   il += ir;
   if(il != 7){
     lrc = 66;
     if(prlc) printf(f,lrc);
   }
   il = 5; lr = 2;
   il += lr;
   if(il != 7){
     lrc = 67;
     if(prlc) printf(f,lrc);
   }
   il = 5; ur = 2;
   il += ur;
   if(il != 7){
     lrc = 68;
     if(prlc) printf(f,lrc);
   }
   il = 5; fr = 2;
   il += fr;
   if(il != 7){
     lrc = 69;
     if(prlc) printf(f,lrc);
   }
   il = 5; dr = 2;
   il += dr;
   if(il != 7){
     lrc = 70;
     if(prlc) printf(f,lrc);
   }
   ll = 5; cr = 2;
   ll += cr;
   if(ll != 7){
     lrc = 71;
     if(prlc) printf(f,lrc);
   }
   ll = 5; sr = 2;
   ll += sr;
   if(ll != 7){
     lrc = 72;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ir = 2;
   ll += ir;
   if(ll != 7){
     lrc = 73;
     if(prlc) printf(f,lrc);
   }
   ll = 5; lr = 2;
   ll += lr;
   if(ll != 7){
     lrc = 74;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ur = 2;
   ll += ur;
   if(ll != 7){
     lrc = 75;
     if(prlc) printf(f,lrc);
   }
   ll = 5; fr = 2;
   ll += fr;
   if(ll != 7){
     lrc = 76;
     if(prlc) printf(f,lrc);
   }
   ll = 5; dr = 2;
   ll += dr;
   if(ll != 7){
     lrc = 77;
     if(prlc) printf(f,lrc);
   }
   ul = 5; cr = 2;
   ul += cr;
   if(ul != 7){
     lrc = 78;
     if(prlc) printf(f,lrc);
   }
   ul = 5; sr = 2;
   ul += sr;
   if(ul != 7){
     lrc = 79;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ir = 2;
   ul += ir;
   if(ul != 7){
     lrc = 80;
     if(prlc) printf(f,lrc);
   }
   ul = 5; lr = 2;
   ul += lr;
   if(ul != 7){
     lrc = 81;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ur = 2;
   ul += ur;
   if(ul != 7){
     lrc = 82;
     if(prlc) printf(f,lrc);
   }
   ul = 5; fr = 2;
   ul += fr;
   if(ul != 7){
     lrc = 83;
     if(prlc) printf(f,lrc);
   }
   ul = 5; dr = 2;
   ul += dr;
   if(ul != 7){
     lrc = 84;
     if(prlc) printf(f,lrc);
   }
   fl = 5; cr = 2;
   fl += cr;
   if(fl != 7){
     lrc = 85;
     if(prlc) printf(f,lrc);
   }
   fl = 5; sr = 2;
   fl += sr;
   if(fl != 7){
     lrc = 86;
     if(prlc) printf(f,lrc);
   }
   fl = 5; ir = 2;
   fl += ir;
   if(fl != 7){
     lrc = 87;
     if(prlc) printf(f,lrc);
   }
   fl = 5; lr = 2;
   fl += lr;
   if(fl != 7){
     lrc = 88;
     if(prlc) printf(f,lrc);
   }
   fl = 5; ur = 2;
   fl += ur;
   if(fl != 7){
     lrc = 89;
     if(prlc) printf(f,lrc);
   }
   fl = 5; fr = 2;
   fl += fr;
   if(fl != 7){
     lrc = 90;
     if(prlc) printf(f,lrc);
   }
   fl = 5; dr = 2;
   fl += dr;
   if(fl != 7){
     lrc = 91;
     if(prlc) printf(f,lrc);
   }
   dl = 5; cr = 2;
   dl += cr;
   if(dl != 7){
     lrc = 92;
     if(prlc) printf(f,lrc);
   }
   dl = 5; sr = 2;
   dl += sr;
   if(dl != 7){
     lrc = 93;
     if(prlc) printf(f,lrc);
   }
   dl = 5; ir = 2;
   dl += ir;
   if(dl != 7){
     lrc = 94;
     if(prlc) printf(f,lrc);
   }
   dl = 5; lr = 2;
   dl += lr;
   if(dl != 7){
     lrc = 95;
     if(prlc) printf(f,lrc);
   }
   dl = 5; ur = 2;
   dl += ur;
   if(dl != 7){
     lrc = 96;
     if(prlc) printf(f,lrc);
   }
   dl = 5; fr = 2;
   dl += fr;
   if(dl != 7){
     lrc = 97;
     if(prlc) printf(f,lrc);
   }
   dl = 5; dr = 2;
   dl += dr;
   if(dl != 7){
     lrc = 98;
     if(prlc) printf(f,lrc);
   }
   cl = 5; cr = 2;
   cl -= cr;
   if(cl != 3){
     lrc = 99;
     if(prlc) printf(f,lrc);
   }
   cl = 5; sr = 2;
   cl -= sr;
   if(cl != 3){
     lrc = 100;
     if(prlc) printf(f,lrc);
   }  
   
   if(lrc != 0) {
     rc = 1;
     if(pd0->flgd != 0) printf(s714er,1);
   }
   return rc;
}

#include "cq-main.h"
