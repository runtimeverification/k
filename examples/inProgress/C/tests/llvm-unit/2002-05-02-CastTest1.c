int printf(const char *, ...);

int
main(int argc, char** argv)
{
  signed char c0  = -1;
  unsigned char c1 = 255;
  printf("bs0  = %d %d\n", c0, c1);
  return 0;
}
