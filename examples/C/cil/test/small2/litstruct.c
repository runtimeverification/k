extern void exit(int);

struct Foo {
  int a;
  int b;
} structure;

int main()
{
  char **foo;
  
  structure = ((struct Foo) {3, 4});
  if(structure.a + structure.b != 7) exit(1);


  foo = (char *[]) { "x", "y", "z"};
  if(* foo[1] != 'y') exit(2);
  

  if( ((int[]) { 1, 2, 3})[1] != 2) exit(3);
  
  exit(0);
}

