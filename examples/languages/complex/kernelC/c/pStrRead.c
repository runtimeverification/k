int * arrRead() {
  int n ;
  scanf("%d",&n);
  int * a = (int *)malloc((n+1)*sizeof(int));
  int i = 0;
  while (i != n) {
    scanf("%d",a+i);
    i++;
  }
  a[n]=0;
  return a;
}

