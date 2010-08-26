struct Foo {
    char *name;
    int value;
};
struct Foo debug_table[] = {
    { "", 0x0004  + 0x0002  + 0x0020  + 0x0040  + 0x0100  + 0x0010  + 0x2000  + 0x0800  },
    { "compl",   0x0001 , },{  "essen",       0x0002  },
    { "expand",  0x0004 , },{ "expand1",     0x0008 | 0x0004  },
    { "irred",   0x0020 , },{  "irred1",      0x4000 | 0x0020  },
    { "reduce",  0x0040 , },{ "reduce1",     0x0080 | 0x0040  },
    { "mincov",  0x0800 , },{ "mincov1",     0x1000 | 0x0800  },
    { "sparse",  0x0100 , },{ "sharp",       0x2000  },
    { "taut",    0x0200 , },{   "gasp",        0x0010  },
    { "exact",   0x0400  },
    { 0 },
};

unsigned int debug;

int main()
{
  debug = debug_table[0].value;
  return 0;
}
