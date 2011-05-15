load kernelc-compiled
kmod KERNELC-STRINGS is including KERNELC-SYNTAX 


  macro pStrLen.c =
int strLen(int * a) {
   int l = 0;
   while(* a++) {l++;}
   return l;
}

  macro pStrCpy.c = 
void strCpy(int * a, int * b) {
   while (*a++=*b++) {} 
}







endkm

