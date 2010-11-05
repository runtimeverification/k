typedef double real;

#define DIM 3
typedef real vector[3], matrix[DIM][DIM];


void multiply(matrix a, matrix b) {
  int i, j;
  matrix c;
  
  for(i=0;i<DIM;i++) {
    for(j=0;j<DIM;j++) {
      real sum = 0.0;
      int  k;
      for(k=0;k<DIM;k++) {
        sum += a[i][k] * b[k][j];
      }
      c[i][j] = sum;
    }
  }
}

int main() {
  return 0;
}
