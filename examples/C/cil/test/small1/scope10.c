int blah()
{
        static float test = 0;
        test++;
}
 
static int test = 0;
 
int main(int argc, char **argv)
{
        blah();
        test = 1;
        return 0;
}
