/* We test that the merger does not borrow the top-level const attribute for 
 * a global declared extern to the definition. Because if the definition is 
 * const then we might not be able to write it to it at all */
extern const struct { int f; } x;


int read() {
  return x.f;
}
