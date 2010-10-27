//===--- matrix.c --- Test Cases for Bit Accurate Types -------------------===//
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This is a test for matrix with non-regular bitwidth data. In
// my_test(A, B) function, we get A=A*B. For each row after
// multiplication, we sort it in non-increasing order. Then the first
// two largest elements are used to get the gcd.
//
//===----------------------------------------------------------------------===//


#include "bits.h"
#include <stdio.h>
#include <stdlib.h>

typedef enum bool{false=0, true=1} bool;

void mysort(const int24  X[8], int24  Y[8])
{
  unsigned int i, j;
  int24 temp;
  {
    j = 0;
    for ( ; ; ) {
      bool ssdm_tmp_4 = (j < 8);
      if (!ssdm_tmp_4) break;
      Y[j] = X[j];
      j++;
    }
  }
  {
    j = 0;
    for ( ; ;j++ ) {
      bool ssdm_tmp_5 = (j < 8);
      if (!ssdm_tmp_5) break;
      {
        i = j;
        for ( ; ; i++) {
          bool ssdm_tmp_6 = (i < 8);
          if (!ssdm_tmp_6) break;
          {
            if(Y[i]>Y[j]){
              temp = Y[j];
              Y[j] = Y[i];
              Y[i] = temp;
            }
                                
          }
        }
      }

    }
  }
}



int get_gcd(const int  a, const int  b)
{
  if (b == 0)
    return a;
  
  return get_gcd( b, a % b );
}



int my_test(int24  A[8][8], int24  B[8][8])
{
  unsigned int i, j, k, dd;
  int24 C[8][8];
  int24 D[8];
  int t;
  {
    i = 0;
    for ( ; ; ) {
      bool ssdm_tmp_1 = (i < 8);
      if (!ssdm_tmp_1) break;
      {
        j = 0;
        for ( ; ; ) {
          bool ssdm_tmp_2 = (j < 8);
          if (!ssdm_tmp_2) break;
          {
            {
              C[i][j] = 0;
              k = 0;
              for ( ; ; ) {
                bool ssdm_tmp_3 = (k < 8);
                if (!ssdm_tmp_3) break;
                C[i][j] += A[i][k] * B[k][j];
                ++k;
              }
            }
                       
          }
                   
          ++j;
        }
      }
      mysort(C[i], D);
      t = get_gcd(D[0], D[1]);
      printf("get_gcd(%d, %d) = %d\n", D[0], D[1], t);
      ++i;
    }
  }
  return 0;
}




int main()
{
  int i, j;
            
  int24 X[8][8];
  int24 Y[8][8];

  for(i=0; i<8; i++)
    for(j=0; j<8; j++){
      X[i][j] = (i+1) * (j + 79);
      Y[i][j] = (i-1) * (j + 255);
    }
  my_test(X, Y);

  return 0;
}


