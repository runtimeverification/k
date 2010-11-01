int * z1[6] __SIZED;
void foo1(void *y) {
  int * * p = & z1[3]  ;

  int * * a = p + z1[2][2];
}

extern void* malloc(unsigned int);

void foo2() {
  int * * p = (int * *)malloc(20);
  p ++;
  {
    int ***q = (int***)p;
  }
}
