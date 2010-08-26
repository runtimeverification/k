// test storing ints in pointers


int main()
{
  // local variable
  int local = 7;

  // pointer to this variable
  int *ptr = &local;
  *ptr = 9;            // modify via pointer

  // now store an int in the ptr
  ptr = (int*)23;
  local = (int)ptr;    // read the int out of the ptr

  // point the ptr back at the local
  ptr = &local;

  // and verify everything is 23
  return *ptr + local*10 - (23 + 23*10);
}
