typedef struct pthread_mutex_t pthread_mutex_t;

struct __Q2_4_STL6locale
{
  struct __Q2_4_STL12_Locale_impl *_M_impl;
};


typedef int int_type;
typedef int_type int_type1;
struct str1
{
  int *_M_get;
};

__inline static int_type1 sbump (struct str1 *this);

__inline static int_type1 sbump (struct str1 *this)
{
  int tmp___3;
  char const *tmp___4;
  int tmp___5;
  {
    tmp___5 = 5;
    if (tmp___5 > 0)
      {
	tmp___4 = 0;
      }
    return (tmp___3);
  }
}

__inline static int_type1 sbump___0  (struct str1 *this)
{
  int tmp___3;
  char const *tmp___4;
  int tmp___5;
  {
    tmp___5 = 5;
    if (tmp___5 > 0)
      {
	tmp___4 = 0;
      }
    return (tmp___3);
  }
}

int main(int argc, char *argv)
{
  if (argc > 100) {    // gcc doesn't know this is always false
    sbump___0(0);      // if actually called, this segfaults
  }
  return 0;
}
