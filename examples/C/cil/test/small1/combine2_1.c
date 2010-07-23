/* Declare it as an array but without length */
extern char* foo[];

/* Now it has a length but is global */
char *foo[2] = {"first string", "second string"};
 
extern int bar;

int f1() {
  return bar;
}
