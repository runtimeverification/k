// # %W% %G% %U%
// #
// # 1987 makefile
// #
// # Copyright (c) 1987, Landon Curt Noll & Larry Bassel.
// # All Rights Reserved.  Permission for personal, educational or non-profit
// # use is granted provided this this copyright and notice are included in its
// # entirety and remains unaltered.  All other uses must receive prior permission
// # from Landon Curt Noll and Larry Bassel.

// Worst Style:

	// Spencer Hines
	// OnLine Computer Systems
	// 4200 Farragut Street
	// Hyattsville, MD
	// 20781
	// USA

// Try:  hines hines.c

// This program was designed to maximize the bother function for
// structured programmers.  This program takes goto statements to their
// logical conclusion.  The layout and choice of names are classic.

// We consider this to be a beautiful counter-example for Frank Rubin's
// letter to ACM form titled: `` "GOTO Considered Harmful" Considered Harmful ''.
// See the Communications of the ACM, March 1987, Page 195-196.

// Copyright (c) 1987, Landon Curt Noll & Larry Bassel.
// All Rights Reserved.  Permission for personal, educational or non-profit use is
// granted provided this this copyright and notice are included in its entirety
// and remains unaltered.  All other uses must receive prior permission in writing
// from both Landon Curt Noll and Larry Bassel.


#include <stdio.h>
//#include <malloc.h>
#include <stdlib.h>
#include <string.h>

main(togo,toog)
int togo;
char *toog[];
{char *ogto,   tgoo[90];FILE  *ogot;  int    oogt=0, ootg,  otog=89,
ottg=1;if (    togo==  ottg)   goto   gogo;  goto    goog;  ggot:
if (   fgets(  tgoo,   otog,   ogot)) goto   gtgo;   goto   gott;
gtot:  exit(0); ogtg: ++oogt;   goto   ogoo;  togg:   if (   ootg > 0)
goto   oggt;   goto    ggot;   ogog:  if (  !ogot)   goto   gogo;
goto   ggto;   gtto:   printf( "%d    goto   \'s\n", oogt); goto
gtot;  oggt:   if (   !memcmp( ogto, "goto", 4))     goto   otgg;
goto   gooo;   gogo:   exit(   ottg); tggo:  ootg=   strlen(tgoo);
goto   tgog;   oogo: --ootg;   goto   togg;  gooo: ++ogto;  goto
oogo;  gott:   fclose( ogot);  goto   gtto;  otgg:   ogto=  ogto +3;
goto   ogtg;   tgog:   ootg-=4;goto   togg;  gtgo:   ogto=  tgoo;
goto   tggo;   ogoo:   ootg-=3;goto   gooo;  goog:   ogot=  fopen(
toog[  ottg],  "r");   goto    ogog;  ggto:  ogto=   tgoo;  goto
ggot;}
