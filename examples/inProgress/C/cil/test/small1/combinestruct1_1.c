/* test merging of structures whose field names differ */

struct A {
  int x;
};
                            
/* make A's type part of the interface */
extern struct A *connection;          

/* refer to A::x */
int foo()
{
  return connection->x;
}
