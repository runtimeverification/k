


int foo(int x) {
  switch(x) {
  case 6: x ++;
  case 7 ... 10: return foo(x + 2);
  case 'A' ... 'E' : return foo (x + 8);
  case 'F' ... 'Z' : return x;
  default:
    return foo (x + 5);
  }
}

int main() {

  return (foo(6) - 74);
}
 
