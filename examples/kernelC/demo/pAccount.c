load kernelc-compiled-demo
load kernelc-syntax
load kernelc-threads-syntax
kmod KERNELC-ACCOUNT is including KERNELC-THREADS-SYNTAX 
macro pAccount =




int *newAccount(int m) {
  int *a = (int *)malloc(1*sizeof(int));
  *a = m;
  return a;
}

int balance(int *a) {
  acquire(a);
  int b = * a;
  release(a);
  return b;
}

void deposit(int *a, int m) {
  acquire(a);
  *a = *a+m;
  release(a);
}

void withdraw(int *a, int m) {
  acquire(a);
  if (m <= *a) {
    *a = *a - m;
  }
  release(a);
}


void transfer(int *a, int *b, int m) {
  acquire(a);
  if (m <= *a) {
    *a = *a-m;
    *b = *b+m;
  }
  release(a);
}

void run(int *a, int *b) {
  deposit(a, 300);
  withdraw(a, 100);
  transfer(a, b, 100);
}

int main() {
  int *a = newAccount(100);
  int *b = newAccount(20);
  printf("%d;", balance(a));
  printf("%d;", balance(b));
  int t1 = spawn(run(a, b));
  int t2 = spawn(run(b, a));
  join(t1); join(t2);
  printf("%d;", balance(a));
  printf("%d;", balance(b));
}









syntax Pgm ::= pAccount 
syntax Id ::= m | a | b | newAccount | balance | deposit | withdraw | transfer
            | t1 | t2 | run
endkm

  
