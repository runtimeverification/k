/* test support for large constants in enums (gcc-specific) 
   if you ask me, gcc's behaviour is a bit weird, but... */
enum fun {
  SMALL = 33,
  STRANGE = 44LL,
  LARGE = 22LL << 34
};

int main()
{
  int ok = 1;

  ok = ok && (typeof(SMALL))-1 < 0;

  return ok ? 0 : 2;
}
