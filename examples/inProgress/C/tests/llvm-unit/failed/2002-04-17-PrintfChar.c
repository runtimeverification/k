/* this little micro testcase is due to lli printing out char values 
 * incorrectly through printf.
 */
int printf(const char*, ...);

void printArgsNoRet(char a3, char* a5) {
  printf("'%c' '%c'\n", (int)a3, (int)*a5);
}

int main() {
  printArgsNoRet('c', "e");
  return 0;
}
