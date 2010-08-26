
union indir {
  int data; // always odd
  union indir *next; // always even
};

union indir *a; // an array


int foo() {
  int i, acc = 0;
  for(i=0;i<100;i++) {
    union indir e = a[i];
    while(e.data % 2 == 0) e = * e.next;
    acc += (e.data >> 1);
  }
  return acc;
}
