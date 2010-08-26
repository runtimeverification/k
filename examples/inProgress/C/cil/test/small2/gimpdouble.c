// gimpdouble.c
// examples of gimp's usage of doubles and enums

typedef enum {
  ZERO,
  ONE
} Something;

int main()
{
  double d;
  Something s;

  d = ZERO;   
  s = d;
  
  return s;
}

