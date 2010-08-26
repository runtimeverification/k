void vadd (const double * restrict a,
           const double * restrict b,
           double * restrict c,
           int n)
{
  int i;
  for(i=0;i<n;i++) c[i]=a[i]+b[i];
}

int main() {
  double a[10], b[10], c[10];
  vadd(a, b, c, 10);
  
}
