typedef struct foo {
    int x;
    int *y;
} Foo;

Foo * xlarg(Foo **pargs) {
    void * make_me_wild = pargs;
    return *pargs; 
}

Foo * xeval(Foo *args) {
    Foo * expr = xlarg(& args);
}
