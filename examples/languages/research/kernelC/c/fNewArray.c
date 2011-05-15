int * newArray() {
  int n ;
  scanf("%d",&n);
  int * a = (int *)malloc((n+1)*sizeof(int));
  a[0]=n;
  int i = 1;
  while (i <= n) {
    scanf("%d",a+i);
    i = i + 1;
  }
  return a;
}


