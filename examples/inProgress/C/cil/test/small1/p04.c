
void P();
int x1,x2,x3;

void P() {
  if (x1>5) {
    x1=x1+x2+1;
    x3=x3+1;
    P();
    x1=x1-x2;
  }
}

void main() {
  x2 = x1;
  x3=0;
  P();
  x1=x1-x2-x3;
}
