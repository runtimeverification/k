int blah()
{
        static float test = 0;
        test++;
}
 
int test = 0;
 
int main(int argc, char **argv)
{
        blah();
        return 0;
}
