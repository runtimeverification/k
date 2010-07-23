#include "testharness.h"

//Make sure we read and generate escapes correctly
char escapes[]=
   "\0\1\2\3\4\5\6\a\b\t\n\v\f\r\016\017"
   "\x10\x11\x12\x13\x14\x15\x16\x17\x18\x19\x1a\x1b\x1c\x1d\x1e\x1f"
   "\x20\x21\"\x23\x24\x25\x26\x27\x28\x29\x2a\x2b\x2c\x2d\x2e\x2f"
   "\x30\x31\x32\x33\x34\x35\x36\x37\x38\x39\x3a\x3b\x3c\x3d\x3e\x3f"
   "\x40\x41\x42\x43\x44\x45\x46\x47\x48\x49\x4a\x4b\x4c\x4d\x4e\x4f"
   "\x50\x51\x52\x53\x54\x55\x56\x57\x58\x59\x5a\x5b\\\x5d\x5e\x5f"
   "\x60\x61\x62\x63\x64\x65\x66\x67\x68\x69\x6a\x6b\x6c\x6d\x6e\157"
   "\x70\x71\x72\x73\x74\x75\x76\x77\x78\x79\x7a\x7b\x7c\x7d\x7e\x7f"
   "\x80\x81\x82\x83\x84\x85\x86\x87\x88\x89\x8a\x8b\x8c\x8d\x8e\x8f";


//This fails on CCured when i gets to 0x80 because of sign extension problems.
//CCured drops some intermediate casts, assuming that they have no effect, 
//but this is a problem for sign extension on scalars.  In this case,
//   (unsigned char)escapes[i]  != i 
//becomes 
//   (int)(unsigned char)escapes[i]  != (int)i 
//in BinOp.  But CCured then omits the unsigned char cast and does this:
//   (int)escapes[i]  != (int)i 
//which does a sign-extended conversion to it when it shouldn't.

int main(){
  unsigned char i;
  for (i = 0; i < 144; i++){
    if ((unsigned char)escapes[i] != i) {
      printf("escapes[%d] = 0x%x\n", i, escapes[i]);
      E(i);
    }
  }
  
  SUCCESS;
}
