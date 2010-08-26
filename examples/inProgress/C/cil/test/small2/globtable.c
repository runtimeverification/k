// a global table

int nums[] = { 1,2,3 };

struct Foo {
  int a,b;
};
struct Foo foos[] = { {4,5}, {6,7} };

int main()
{
  return nums[1] - 2 +
         foos[0].b - 5;
}
