struct inner {
  int field;
};


struct outer {
  const struct inner inner;
};


int main()
{
  struct outer outer = { { 0 } };
  return outer.inner.field;
}
