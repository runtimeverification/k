//Test that the variable __cil_tmp7 (which may have come from an earlier pass
//through cil) doesn't conflict with any new vars added by CIL.

int** foo() { return (int**)0;}

int main() {
  char* __cil_tmp7 = 0;
  return (int)foo() + (int)foo() + **foo();
}
