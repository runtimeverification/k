/* test support for large constants in enums (gcc-specific) 
   if you ask me, gcc's behaviour is a bit weird, but... */
enum fun {
  SMALL = 33,
};

int main()
{
  int ok = 1;

  ok = ok && (enum fun)-1 > 0;

  return ok ? 0 : 2;
}
