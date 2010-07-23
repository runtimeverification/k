// volatilestruct.c
// from sac at stevechamberlain dot com

// problem with associating attributes with structs instead
// of the declared instances

struct foo
{
  int AAAAAAAAAAAAAAAAAAA:7;
} xxx;

int main ()
{
  struct foo
  {
    double BBBBBBBBBBBBBBBBBBB;
  } volatile bar;

  static struct foo baz;
  bar = baz;

  return 0;
}
