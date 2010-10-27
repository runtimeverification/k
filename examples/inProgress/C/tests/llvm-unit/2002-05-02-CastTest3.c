int printf(const char *, ...);

int main(int argc, char** argv) {
  short s1 = (argc >= 3)? argc : -769; /* 0xf7ff = -769 */

  unsigned short us2 = (unsigned short) s1;     /* 0xf7ff = 64767 */
  
  printf("s1   = %d\n",   s1);
  printf("us2  = %u\n",   us2);
  return 0;
}
