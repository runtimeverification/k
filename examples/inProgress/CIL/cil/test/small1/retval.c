
typedef struct rbNode {
    int filler;
    char data[0];
} RBNode; 

char * ret_field(RBNode * r) {
    return & (r->data[0]);
}
