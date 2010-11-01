// enums where one tag is init'd with another

int printf(char const *fmt, ...);

// this was messing up the parser
enum __rlimit_resource {
  _RLIMIT_CPU = 0,
  RLIMIT_CPU = _RLIMIT_CPU,
  _RLIMIT_FSIZE = 1,
  RLIMIT_FSIZE = _RLIMIT_FSIZE,
  _RLIMIT_DATA = 2,
  RLIMIT_DATA = _RLIMIT_DATA,
};

#define PVAL(val) printf(#val " = %d\n", val)

int main()
{
  printf("whazzup?!\n");
  PVAL(_RLIMIT_CPU);
  PVAL(RLIMIT_CPU);
  PVAL(_RLIMIT_FSIZE);
  PVAL(RLIMIT_FSIZE);
  PVAL(_RLIMIT_DATA);
  PVAL(RLIMIT_DATA);
  return 0;
}
