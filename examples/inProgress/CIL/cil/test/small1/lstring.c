typedef unsigned short wchar_t; 
typedef wchar_t WCHAR;
typedef wchar_t *WCHARP;

int fun_accepting_wchar(WCHARP arg) {
  int i;
  char * ptr = (char *)arg; 
  for (i=0;i<10;i++) 
    printf("byte %d = '%c'\n",i,ptr[i]);
  return 0;
}

int main() {
  fun_accepting_wchar(L"Hello, world.\n"); 
  return 0; 
}
/* Correct Output (microsoft command line compiler):
byte 0 = 'H'
byte 1 = ''
byte 2 = 'e'
byte 3 = ''
byte 4 = 'l'
byte 5 = ''
byte 6 = 'l'
byte 7 = ''
byte 8 = 'o'
byte 9 = ''
*/
