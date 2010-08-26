enum fun {
  HMM = (1ULL << 32)
};

int main()
{
  int ok = 1;

  /* HMM is signed - types are based on value, not the defining expression */
  ok = ok && (typeof(HMM))-1 < 0;

  return ok ? 0 : 2;
}
