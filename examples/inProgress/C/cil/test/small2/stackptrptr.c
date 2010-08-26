// stackptrptr.c  
// NUMERRORS(1)
// demonstrate problem with stack ptr to stack ptr

#define MESS_UP      // ERROR(1)

#ifndef MESS_UP
  int main()
  {
    int x = 0;
    int *px = &x;
    int **ppx = &px;     // allowed

    return **ppx;
  }

#else
  int main()
  {
    int x = 0;
    int *px = &x;
    int *ppx[1];

    ppx[0] = &px;         // not allowed
    return *(ppx[0]);
  }
#endif // 0/1
