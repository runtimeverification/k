struct rusage ;

struct foobar_not_used;

int w3(struct rusage *__usage ) { return 0; }

int main()
{
  struct rusage *r;
  w3(r);
  return 0;
}

