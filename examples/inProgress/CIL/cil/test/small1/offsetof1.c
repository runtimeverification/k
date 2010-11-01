
struct align_short {
    char c;
    short a;
};



int main()
{
    int align_of_short;

    align_of_short	= 
    (((char*)&(((struct align_short  *)0)->a)) - ((char*)0)) ;

    return 0 ;
}

