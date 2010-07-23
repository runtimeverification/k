typedef struct {
    int x;
} IntStruct;

int y;

int main() {
    int * ip = &y;
    IntStruct * sp;

    sp = ip;

    return sp->x;
}
