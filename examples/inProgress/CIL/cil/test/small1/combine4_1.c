/* A simple test with two files, no structs. The second file refers to the 
 * same exact types and to foo */
typedef int __intptr_t;
typedef __intptr_t intptr_t;

intptr_t foo(void) { return 0; }
