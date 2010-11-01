// thing.c
// strange casts to 'void' on pointer comparisons??

struct Thing *thing;

int test()
{
  return thing == 0;
}

int main()
{
  test();
  return 0;
}
