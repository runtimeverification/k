   int printf(const char *format, ...);
   struct defs {
     int cbits;          /* No. of bits per char           */
     int ibits;          /*                 int            */
     int sbits;          /*                 short          */
     int lbits;          /*                 long           */
     int ubits;          /*                 unsigned       */
     int fbits;          /*                 float          */
     int dbits;          /*                 double         */
     float fprec;        /* Smallest number that can be    */
     float dprec;        /* significantly added to 1.      */
     int flgs;           /* Print return codes, by section */
     int flgm;           /* Announce machine dependencies  */
     int flgd;           /* give explicit diagnostics      */
     int flgl;           /* Report local return codes.     */
     int rrc;            /* recent return code             */
     int crc;            /* Cumulative return code         */
     char rfs[8];        /* Return from section            */
   };

long pow2(long n) {        /* Calculate 2**n by multiplying, not shifting  */
   long s;
   s = 1;
   while(n--) s = s*2;
   return s;
}


void zerofill(char* x) {
   int j;

   for (j=0; j<256; j++) *x++ = 0;
}
int sumof(char* x) {
   char *p;
   int total, j;

   p = x;
   total = 0;

   for(j=0; j<256; j++) total = total+ *p++;
   return total;
}

int extvar;

int setupTable(pd0)                  /*  2.6  Hardware Characteristics     */
struct defs *pd0;
{
   static char qs26[8] = "s26    ";
   char *ps, *pt;
   unsigned char c0, c1;
   float temp, one, delta;
   double tempd, oned;
   static char s[] = "%3d bits in %ss.\n";
   // cme %e to %f
   static char s2[] = "%f is the least number that can be added to 1. (%s).\n";

   ps = qs26;
   pt = pd0->rfs;

   while(*pt++ = *ps++);

          /* Here, we shake the machinery a little to see what falls
             out.  First, we find out how many bits are in a char.  */

   pd0->cbits = 0;
   c0 = 0;
   c1 = 1;

   // cme: this assumes signed overflow behaves in a particular way
   while(c0 != c1) {
     c1 = c1<<1;
     pd0->cbits = pd0->cbits+1;
   }
          /* That information lets us determine the size of everything else. */

   pd0->ibits = pd0->cbits * sizeof(int);
   pd0->sbits = pd0->cbits * sizeof(short);
   pd0->lbits = pd0->cbits * sizeof(long);
   pd0->ubits = pd0->cbits * sizeof(unsigned);
   pd0->fbits = pd0->cbits * sizeof(float);
   pd0->dbits = pd0->cbits * sizeof(double);

          /* We have now almost reconstructed the table in section 2.6, the
             exception being the range of the floating point hardware.
             Now there are just so many ways to conjure up a floating point
             representation system that it's damned near impossible to guess
             what's going on by writing a program to interpret bit patterns.
             Further, the information isn't all that useful, if we consider
             the fact that machines that won't handle numbers between 10**30
             and 10**-30 are very hard to find, and that people playing with
             numbers outside that range have a lot more to worry about than
             just the capacity of the characteristic.

             A much more useful measure is the precision, which can be ex-
             pressed in terms of the smallest number that can be added to
             1. without loss of significance. We calculate that here, for
             float and double.                       */

   one = 1.;
   delta = 1.;
   temp = 0.;
   while(temp != one) {
     temp = one+delta;
     delta = delta/2.;
   }
   pd0->fprec = delta * 4.;
   oned = 1.;
   delta = 1.;
   tempd = 0.;
   while(tempd != oned) {
     tempd = oned+delta;
     delta = delta/2.;
   }
   pd0->dprec = delta * 4.;

          /* Now, if anyone's interested, we publish the results.       */

   // if(pd0->flgm != 0) {
     // printf(s,pd0->cbits,"char");
     // printf(s,pd0->ibits,"int");
     // printf(s,pd0->sbits,"short");
     // printf(s,pd0->lbits,"long");
     // printf(s,pd0->ubits,"unsigned");
     // printf(s,pd0->fbits,"float");
     // printf(s,pd0->dbits,"double");
     // printf(s2,pd0->fprec,"float");
     // printf(s2,pd0->dprec,"double");
   // }
          /* Since we are only exploring and perhaps reporting, but not 
             testing any features, we cannot return an error code.  */

   return 0;
}

int svtest(int n) {
   static k;
   int rc;
   switch (n) {

     case 0: k = 1978;
             rc = 0;
             break;

     case 1: if(k != 1978) rc = 1;
             else{
              k = 1929;
              rc = 0;
             }
             break;

     case 2: if(k != 1929) rc = 1;
             else rc = 0;
             break;
   }
   return rc;
}
zero(){                 /* Returns a value of zero, possibly */
   static k;            /* with side effects, as it's called */
   int rc;              /* alternately with svtest, above,   */
   k = 2;               /* and has the same internal storage */
   rc = 0;              /* requirements.                     */
   return rc;
}
testev(){
   if(extvar != 1066) return 1;
   else return 0;
}

void setev(){                  /* Sets an external variable. Used  */
   extern int extvar;     /* by s4, and should be compiled    */
   extvar = 1066;         /* separately from s4.              */
}


McCarthy(x)
int x;
{
   if(x>100) return x-10;
   else return McCarthy( McCarthy(x+11));
}
int clobber(x,y)
int x, *y;
{
   x = 3;
   *y = 2;
   return 0;
}
