int
main ( int argc, char** argv)
{
  int i;
  int result;
  result = 1;
  for (i = 2; i <= argc+2; i++)
    {
      if ((i & 1) == 0)
	{
	    result = result + 17;
	}
    }
  return result != 35;
}
