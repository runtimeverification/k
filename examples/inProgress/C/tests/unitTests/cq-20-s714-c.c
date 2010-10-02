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
   cl = 5; ir = 2;
   cl -= ir;
   if(cl != 3){
     lrc = 101;
     if(prlc) printf(f,lrc);
   }
   cl = 5; lr = 2;
   cl -= lr;
   if(cl != 3){
     lrc = 102;
     if(prlc) printf(f,lrc);
   }
   cl = 5; ur = 2;
   cl -= ur;
   if(cl != 3){
     lrc = 103;
     if(prlc) printf(f,lrc);
   }
   cl = 5; fr = 2;
   cl -= fr;
   if(cl != 3){
     lrc = 104;
     if(prlc) printf(f,lrc);
   }
   cl = 5; dr = 2;
   cl -= dr;
   if(cl != 3){
     lrc = 105;
     if(prlc) printf(f,lrc);
   }
   sl = 5; cr = 2;
   sl -= cr;
   if(sl != 3){
     lrc = 106;
     if(prlc) printf(f,lrc);
   }
   sl = 5; sr = 2;
   sl -= sr;
   if(sl != 3){
     lrc = 107;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ir = 2;
   sl -= ir;
   if(sl != 3){
     lrc = 108;
     if(prlc) printf(f,lrc);
   }
   sl = 5; lr = 2;
   sl -= lr;
   if(sl != 3){
     lrc = 109;
     if(prlc) printf(f,lrc);
   }
   sl = 5; ur = 2;
   sl -= ur;
   if(sl != 3){
     lrc = 110;
     if(prlc) printf(f,lrc);
   }
   sl = 5; fr = 2;
   sl -= fr;
   if(sl != 3){
     lrc = 111;
     if(prlc) printf(f,lrc);
   }
   sl = 5; dr = 2;
   sl -= dr;
   if(sl != 3){
     lrc = 112;
     if(prlc) printf(f,lrc);
   }
   il = 5; cr = 2;
   il -= cr;
   if(il != 3){
     lrc = 113;
     if(prlc) printf(f,lrc);
   }
   il = 5; sr = 2;
   il -= sr;
   if(il != 3){
     lrc = 114;
     if(prlc) printf(f,lrc);
   }
   il = 5; ir = 2;
   il -= ir;
   if(il != 3){
     lrc = 115;
     if(prlc) printf(f,lrc);
   }
   il = 5; lr = 2;
   il -= lr;
   if(il != 3){
     lrc = 116;
     if(prlc) printf(f,lrc);
   }
   il = 5; ur = 2;
   il -= ur;
   if(il != 3){
     lrc = 117;
     if(prlc) printf(f,lrc);
   }
   il = 5; fr = 2;
   il -= fr;
   if(il != 3){
     lrc = 118;
     if(prlc) printf(f,lrc);
   }
   il = 5; dr = 2;
   il -= dr;
   if(il != 3){
     lrc = 119;
     if(prlc) printf(f,lrc);
   }
   ll = 5; cr = 2;
   ll -= cr;
   if(ll != 3){
     lrc = 120;
     if(prlc) printf(f,lrc);
   }
   ll = 5; sr = 2;
   ll -= sr;
   if(ll != 3){
     lrc = 121;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ir = 2;
   ll -= ir;
   if(ll != 3){
     lrc = 122;
     if(prlc) printf(f,lrc);
   }
   ll = 5; lr = 2;
   ll -= lr;
   if(ll != 3){
     lrc = 123;
     if(prlc) printf(f,lrc);
   }
   ll = 5; ur = 2;
   ll -= ur;
   if(ll != 3){
     lrc = 124;
     if(prlc) printf(f,lrc);
   }
   ll = 5; fr = 2;
   ll -= fr;
   if(ll != 3){
     lrc = 125;
     if(prlc) printf(f,lrc);
   }
   ll = 5; dr = 2;
   ll -= dr;
   if(ll != 3){
     lrc = 126;
     if(prlc) printf(f,lrc);
   }
   ul = 5; cr = 2;
   ul -= cr;
   if(ul != 3){
     lrc = 127;
     if(prlc) printf(f,lrc);
   }
   ul = 5; sr = 2;
   ul -= sr;
   if(ul != 3){
     lrc = 128;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ir = 2;
   ul -= ir;
   if(ul != 3){
     lrc = 129;
     if(prlc) printf(f,lrc);
   }
   ul = 5; lr = 2;
   ul -= lr;
   if(ul != 3){
     lrc = 130;
     if(prlc) printf(f,lrc);
   }
   ul = 5; ur = 2;
   ul -= ur;
   if(ul != 3){
     lrc = 131;
     if(prlc) printf(f,lrc);
   }
   ul = 5; fr = 2;
   ul -= fr;
   if(ul != 3){
     lrc = 132;
     if(prlc) printf(f,lrc);
   }
   ul = 5; dr = 2;
   ul -= dr;
   if(ul != 3){
     lrc = 133;
     if(prlc) printf(f,lrc);
   }
   fl = 5; cr = 2;
   fl -= cr;
   if(fl != 3){
     lrc = 134;
     if(prlc) printf(f,lrc);
   }
   fl = 5; sr = 2;
   fl -= sr;
   if(fl != 3){
     lrc = 135;
     if(prlc) printf(f,lrc);
   }
   fl = 5; ir = 2;
   fl -= ir;
   if(fl != 3){
     lrc = 136;
     if(prlc) printf(f,lrc);
   }
   fl = 5; lr = 2;
   fl -= lr;
   if(fl != 3){
     lrc = 137;
     if(prlc) printf(f,lrc);
   }
   fl = 5; ur = 2;
   fl -= ur;
   if(fl != 3){
     lrc = 138;
     if(prlc) printf(f,lrc);
   }
   fl = 5; fr = 2;
   fl -= fr;
   if(fl != 3){
     lrc = 139;
     if(prlc) printf(f,lrc);
   }
   fl = 5; dr = 2;
   fl -= dr;
   if(fl != 3){
     lrc = 140;
     if(prlc) printf(f,lrc);
   }
   dl = 5; cr = 2;
   dl -= cr;
   if(dl != 3){
     lrc = 141;
     if(prlc) printf(f,lrc);
   }
   dl = 5; sr = 2;
   dl -= sr;
   if(dl != 3){
     lrc = 142;
     if(prlc) printf(f,lrc);
   }
   dl = 5; ir = 2;
   dl -= ir;
   if(dl != 3){
     lrc = 143;
     if(prlc) printf(f,lrc);
   }
   dl = 5; lr = 2;
   dl -= lr;
   if(dl != 3){
     lrc = 144;
     if(prlc) printf(f,lrc);
   }
   dl = 5; ur = 2;
   dl -= ur;
   if(dl != 3){
     lrc = 145;
     if(prlc) printf(f,lrc);
   }
   dl = 5; fr = 2;
   dl -= fr;
   if(dl != 3){
     lrc = 146;
     if(prlc) printf(f,lrc);
   }
   dl = 5; dr = 2;
   dl -= dr;
   if(dl != 3){
     lrc = 147;
     if(prlc) printf(f,lrc);
   }
   cl = 5; cr = 2;
   cl *= cr;
   if(cl != 10){
     lrc = 148;
     if(prlc) printf(f,lrc);
   }
   cl = 5; sr = 2;
   cl *= sr;
   if(cl != 10){
     lrc = 149;
     if(prlc) printf(f,lrc);
   }
   cl = 5; ir = 2;
   cl *= ir;
   if(cl != 10){
     lrc = 150;
     if(prlc) printf(f,lrc);
   }

   
   if(lrc != 0) {
     rc = 1;
     if(pd0->flgd != 0) printf(s714er,1);
   }
   return rc;
}

#include "cq-main.h"
