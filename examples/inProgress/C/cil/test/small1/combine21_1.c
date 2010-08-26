static int gflag;

__inline void testit ( int flag )
{
        gflag = flag;
}

extern void otest(int flag);

int
main(int argc, char **argv)
{
        testit(0);
        otest(2);
        testit(1);
        return 0;
}
