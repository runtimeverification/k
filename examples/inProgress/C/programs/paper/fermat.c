int main(void){
  const int MAX = 5;
  int a=1,b=1,c=1;
  while ((c*c*c) != ((a*a*a)+(b*b*b))) {
    a++;
    if (a>MAX) {
      a=1;
      b++;
    }
    if (b>MAX) {
      b=1;
      c++;
    }
    if (c>MAX) {
      c=1;
    }
  }
  return 0;
}
