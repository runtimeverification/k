int main() {
    static unsigned char buf[16];
    unsigned char * bp = buf;
    walk(buf,9);
    return 0;
}

int walk(char * a, int l) {
    int i;

    for (i=0; i<l; i++) {
        a[i] = a[i] + 1;
    }
    return i;
}

