// combinetaggedfn_2.c

// foo will be tagged
int foo(int x);
                         
// wrong type; originally used 'void' but our polymorphism defeats hat
typedef int* (*Func)(int*);

int main()
{            
  Func f;
  int x;

  f = (Func)&foo;    // make foo tagged

  // cast to correct type and invoke
  x = ((int (*)(int))f)(3);
  
  return x-4;
}


