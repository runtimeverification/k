int f(__builtin_va_list vl);
int f(__builtin_va_list vl) {
  return 0;
}
 
int main() {
  __builtin_va_list vl;
  return f(vl);
}
