/*
   chunk1.c - show that the CIL merger fails to rename a symbol when it must.

   In this file, we declare chunk to be a typedef.
   In another file we declare it to be a static variable.
   One of these two must get renamed but neither is.

   Test on Cygwin under Windows XP using CIL 1.2.4

% cilly --save-temps --merge -c chunk1.c C:/cygwin/bin/gcc -D_GNUCC -E -DCIL=1 chunk1.c -o ./chunk1.i

% cilly --save-temps --merge -c chunk2.c C:/cygwin/bin/gcc -D_GNUCC -E -DCIL=1 chunk2.c -o ./chunk2.i

% cilly --save-temps --keepmerged --merge chunk1.o chunk2.o C:/cygwin/home/dlibrik/cil/obj/x86_WIN32/cilly.asm.exe --out ./a.cil.c chunk1.o chunk2.o --mergedout ./a.out_comb.c C:/cygwin/bin/gcc -D_GNUCC -E ./a.cil.c -o ./a.cil.i C:/cygwin/bin/gcc -D_GNUCC -c -o a.out_comb.o ./a.cil.i
chunk2.c:4: error: `chunk' redeclared as different kind of symbol
chunk1.c:8: error: previous declaration of `chunk'

   Investigation of a.cil.c shows that "chunk" has been kept for both names.
   This is clearly a bug, since both typedef and variable should be local.
*/

#include <string.h>

struct chunk_struct {
        char c_tab[20];
        struct chunk_struct *c_prev;
};

typedef struct chunk_struct chunk;


int chunk1(char *s) {

  chunk c;
  
  strcpy(s, c.c_tab);
  
  return c.c_tab[0];
}

