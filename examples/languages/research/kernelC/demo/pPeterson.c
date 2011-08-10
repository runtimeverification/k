load kernelc-syntax
load kernelc-threads-syntax
kmod KERNELC-PETERSON is including KERNELC-THREADS-SYNTAX 
macro pPeterson =




void peterson(int *flag, int *turn, int t) {
  flag[t] = 1;
  *turn = 1-t;
  while (flag[1-t] && *turn == 1-t) {}
  printf("%d;",-1-t);
  printf("%d;", 1+t);
  flag[t] = 0;
}

int main() {
  int* flag = (int *)malloc(2*sizeof(int));
  flag[0] = 0; flag[1] = 0 ;
  int * turn =  (int *)malloc(1*sizeof(int));
  int t1 = spawn(peterson(flag, turn, 0));
  int t2 = spawn(peterson(flag, turn, 1));
  join(t1);
  join(t2);
  return 0;
}










syntax Pgm ::= pPeterson 
syntax #Id ::= flag | turn | t | peterson
            | t1 | t2 
endkm

  
