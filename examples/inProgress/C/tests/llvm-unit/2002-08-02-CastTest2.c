int printf(const char *, ...);

void test(short s1) {
  unsigned short us2 = (unsigned short) s1;     /* 0xf7ff = 64767 */
  
  printf("s1   = %d\n",   s1);
  printf("us2  = %u\n",   us2);
}

int main() {
  test(-769);
  return 0;
}
