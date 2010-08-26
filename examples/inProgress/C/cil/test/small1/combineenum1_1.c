/* Make sure that enumeration isomorphism is lax enough */
enum {
  INT = 0,
  FLOAT,
} x1;


void foo() {
  x1 = FLOAT;
}
