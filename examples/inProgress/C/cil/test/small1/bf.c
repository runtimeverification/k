struct conn_rec {
    void * first_field;
    /*
    unsigned aborted : 1;
    signed int keepalive : 2;
    unsigned keptalive : 1;
    */
    signed int double_reverse : 2;
    int last_field ;
} ;

int main(int argc, char *argv[]) {
    struct conn_rec c;

    printf("%d\n",c.last_field);
    return 0;
}
