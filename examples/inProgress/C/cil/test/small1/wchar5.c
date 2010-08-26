#include <wchar.h>
#include "testharness.h"

//matth: some lexer bugs that I haven't had time to fix


int main(){
  //BUG:  the "i\xabcd" has no L in front, so we treat it like a normal string,
  // and can't handle the big value.

  wchar_t a[] = L"H" "i\xabcd"; 
  // should be the same as:
  wchar_t b[] = L"Hi\xabcd";


  int i;
  for (i = 0; i < 4; i++){
    if (a[i] != b[i]) E(i);
  }
  
  SUCCESS;
}
