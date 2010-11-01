//There's a gcc bug on Cygwin where filenames referring to
//non-existent files can result in large line numbers appearing in the
//preprocessed source.

# 4294967150 "cpp_heap.c"
int main() { return 0; }
