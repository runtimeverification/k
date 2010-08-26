#include <wchar.h>
#include "testharness.h"

int main()
{
  wchar_t aa[] = L"A\xabcd";    // 2 wide chars
  wchar_t ba[] = L"A\\xabcd";   // 7 wide chars
  wchar_t *ap = L"A\xabcd";
  wchar_t *bp = L"A\\xabcd";
  char *p1, *p2; 
  int i;

  if (wcslen(aa) != wcslen(ap)) { E(1); } 
  if (wcslen(ba) != wcslen(bp)) { E(2); } 
  if (wcslen(aa) == wcslen(ba)) { E(3); } 
  if (wcslen(ap) == wcslen(bp)) { E(4); } 

  p1 = aa;
  p2 = ap;
  for (i=0; i<2 * sizeof(wchar_t); i++) {
    if (p1[i] != p2[i]) { E(5); } 
  } 
  p1 = ba;
  p2 = bp; 
  for (i=0; i<7 * sizeof(wchar_t); i++) { 
    if (p1[i] != p2[i]) { E(6); } 
  } 

  if (wcscmp(aa,ap) != 0) { E(7); } 
  if (wcscmp(ba,bp) != 0) { E(8); } 
  if (wcscmp(aa,ba) == 0) { E(9); } 
  if (wcscmp(ap,bp) == 0) { E(10); } 

  SUCCESS; 
} 
