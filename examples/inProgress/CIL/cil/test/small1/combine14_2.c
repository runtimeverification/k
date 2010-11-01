extern int protoname1;

int protoname2 = 5;

void bar(int protoname2);

void foo(int myname) {
  protoname1 = myname;

  bar(0); /* Should set protoname2 */
}
