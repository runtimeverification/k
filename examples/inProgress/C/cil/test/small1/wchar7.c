#include <wchar.h>
#include "testharness.h"

int main()
{
  wchar_t aa[] = L"\"";    // 1 wide char
  wchar_t *ap = L"\"";
  char *p1, *p2; 
  int i;

  if (wcslen(aa) != wcslen(ap)) { E(1); } 
  p1 = aa;
  p2 = ap;
  for (i=0; i<2 * sizeof(wchar_t); i++) {
    if (p1[i] != p2[i]) { E(2); } 
  } 
  if (wcscmp(aa,ap) != 0) { E(3); } 

  SUCCESS; 
} 
