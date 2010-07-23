// combine_node_alloc_1.c
// "Out of memory" problem

struct node {
    struct node *link;
};
struct node *list[1] = {
    ((struct node *) 0)
};
