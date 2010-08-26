/* other half of combinestruct1 */

struct B {
  int y;
} x;

/* connect A and B */
struct B *connection = &x;

/*refer to B::y */
int main()
{
  int whatever;

  whatever = connection->y;
  whatever += foo();    /* for the heck of it */
  
  return whatever - whatever;
}

