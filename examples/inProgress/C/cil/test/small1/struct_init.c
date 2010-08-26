#ifndef __FSEQN
#define __FSEQN
#endif

typedef struct {
    char * name;
    int data;
} cmd;

cmd our_cmds[] = {
    { "command 1", 1 },
    { "command 2", 2 },
    { "command 3", 3 },
    { 0, 0} };

struct {
    int x;
    cmd * cmds;
    int y;
} main_struct = { 
    100,
    our_cmds,
    200
};

int main() {
    char * __FSEQN p = "HELLO";
    return 0;
}

