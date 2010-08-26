static int g;
inline int foo(int x) { return g; }


int getfoo2() { return (int)foo; }
