#include "testharness.h"
#include <stdio.h>
#include <string.h>

//matth: a test to show the difficulty with allowing end+1 access for reads.
// Here, CCured sees that *p can be written to, so it doesn't allow the +1 
// access that would let us read the NUL.

//Normally, CCured solves this problem by adding a second NUL to the string: 
// One the code can access, and one it can't.  But if the string comes 
// from a system call, we can't assume it has two NULs (and CCured will protect
// the one and only NUL from writing).  Here, the __mkptr_string simulates 
// a string returned by a system call.

//To fix this: either change the solver to prevent p from being safe, or
// fix __mkptr_string to allow access to the NUL (probably by making all
// strings returned by __mkptr_string into FSeqs or Seqs, rather than FSeqN
// or SeqN).

void BuildWord(char * pchWord) {
    int i = 0;
    char * pch = pchWord;

    while (1) 
      {
	char* p = pchWord + i; //p is inferred SAFE
	i++;
	if (*p == '\0') 
	  break;
	else
	  *p = 'a';
      }

    printf("%s\n",pchWord); 
}

int main() {
  char buffer[10];
  char* pchWord;
  strcpy(buffer, "foo");

#ifdef CCURED
  pchWord = __mkptr_string(buffer); 
#else
  pchWord = buffer; 
#endif

  BuildWord(pchWord);

  SUCCESS; 
} 
