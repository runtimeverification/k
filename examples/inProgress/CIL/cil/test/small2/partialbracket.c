// partially-bracketed initializers cause problems

struct S {
  int x, y;
};

struct S array[] = {
  1,2,
  3,4
};

struct S array_ok[] = {
  {1,2},
  {3,4}
};

int main() 
{
  return array[0].x - 1;   // should be 0
}
