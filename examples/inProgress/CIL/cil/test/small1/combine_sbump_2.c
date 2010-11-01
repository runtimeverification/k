struct someStruct;

__inline static int sbump (struct someStruct *this)     // --> sbump___0
{
    return (3);
}


__inline static int sbump___0 (struct someStruct *this);     // --> sbump___1
__inline static int sbump___0 (struct someStruct *this)
{
    return (3);
};

foo ()
{
  sbump___0 (0);
}

int main()
{
  foo();
}
