/* Declare it as an array but without length */
extern char* foo[];

/* Now it has a length but is static */
static char *foo[2] = {"first string", "second string"};

static int bar = 0;

static char *foo_static = "My static string";

int f2() {
  return bar;
}
