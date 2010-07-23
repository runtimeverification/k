/* We test isomorphism between structs with different names and anonymous 
 * structs */
struct bar {
  int x;
  struct foo *next;
};

struct foo {
  struct bar b;
} g;

int main() {
  return 0;
}
