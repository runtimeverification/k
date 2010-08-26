// from http://home.comcast.net/~derelict/files/printf2.c
// by and Georges Menie (and Derell Licht?)
#include <stdio.h>

int main (void) {
   int slen ;
   char *ptr = "Hello world!";
   char *np = 0;
   char buf[128];
   printf ("ptr=%s, %s is null pointer, char %c='a'\n", ptr, np, 'a');
   printf ("hex %x = ff, hex02=%02x\n", 0xff, 0);   //  hex handling
   printf ("signed %d = unsigned %u = hex %X\n", -3, -3, -3);   //  int formats
   printf ("%d %s(s) with %%\n", 0, "message");

   slen = sprintf (buf, "justif: left=\"%-10s\", right=\"%10s\"\n", "left", "right");
   printf ("[%d] %s", slen, buf);
   
   sprintf(buf, "padding (pos): zero=[%04d], left=[%-4d], r=[%4d]\n", 3, 3, 3) ;
   printf ("%s", buf);

   //  test walking string builder
   slen = 0 ;
   slen += sprintf(buf+slen, "padding (neg): zero=[%04d], ", -3) ;
   slen += sprintf(buf+slen, "left=[%-4d], ", -3) ;
   slen += sprintf(buf+slen, "right=[%4d]\n", -3) ;
   printf ("[%d] %s", slen, buf);

   sprintf (buf, "%.2f is a double\n", 3.31) ;
   printf ("%s", buf);

   sprintf (buf, "multiple unsigneds: %u %u %2u %X\n", 15, 5, 23, 0xB38F) ;
   printf ("%s", buf);

   sprintf (buf, "multiple chars: %c %c %c %c\n", 'a', 'b', 'c', 'd') ;
   printf ("%s", buf);

   sprintf (buf, "multiple doubles: %.2f %2.0f %.2f %.3f %.2f [%-8.3f]\n",
                  3.31, 2.45, -1.1, 3.093, 13.72, -4.382) ;
   printf ("%s", buf);

   return 0;
}
