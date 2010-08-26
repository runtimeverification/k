// union decl in a compound statement expression

int main()
{
  int status;

  return
    (
      (__extension__
        ({
            union {
              __typeof(  status  ) __in;
              int __i;
            } __u;

            __u.__in = status;
            __u.__i;
          })
      ) & 0xff00
    ) >> 8 ;
}
