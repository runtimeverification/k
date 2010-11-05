extern void exit(int);


// A test with function pointers
typedef int (* FUN1)();


// Fun1 will be a wild function
int fun1(int i1, int* p2, int* p3, int i4) {
  return i1 + *p2 + *p3 + i4;
}

// Now make fun1 a WILD function pointer
FUN1 g = fun1;


int main() {
  int loc1 = 7, loc2 = 9, loc3 = 11;

  // Call fun1 through g
  if(g(5, &loc1, &loc2, 13) != 34)
    exit(1);

  // Call fun1 directly
  if(fun1(1, &loc1, &loc3, 7) != 26) 
    exit(2);

  
  exit(0);
}
