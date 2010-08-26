union Argument {
  int field1;
  char *field2;
} __attribute__ ((__transparent_union__));


int callee(union Argument arg) {
  return *arg.field2 + 1;
}

union Argument mkArgument() {
  union Argument a;
  return a;
}

void caller(void)
{
  char c;
  union Argument a;
  struct {
    double d;
    union Argument a;
  } s;
  
  // It should be Ok to pass individual fields
  callee(5);
  callee(&c);
  /* It should be Ok to pass a whole union also, but the calling convention 
   * will still be that of the first field */
  callee(a);
  callee(s.a);

  /* Now the same thing as above but when the actual argument is not an 
   * lvalue */
  callee(mkArgument());
}

