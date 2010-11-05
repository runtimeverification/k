// neg64.c
// testcase for -2^63 problem
// from sac at stevechamberlain dot com

float
sll2f(s)
     long long int s;
{
  return s;
}

main()
{
  if (sll2f((long long int)(~((~0ULL) >> 1))) != (float)(long long int)~((~0ULL) >> 1)) /* 0x80000000 */
    abort();

  exit(0);
}
