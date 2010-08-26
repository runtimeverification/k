

int * * a; // an array


int foo() {
  int i, acc = 0;
  for(i=0;i<100; i++) {
    int * e = a[i];
    while((int)e % 2 == 0) e = * (int * *) e;
    acc += ((int)e >> 1);
  }
  return acc;         
}
