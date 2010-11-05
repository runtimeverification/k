// decl_mix_stmt.c
// declarations mixed with statements, a-la C99

// NOTE: gcc-2.x does not support this syntax (but 3.x does)

int main()
{
  int x;
  x = 3;
  
  int y;
  y = 6;
  
  return x+y - 9;
}
