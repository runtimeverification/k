typedef int some_type[1];
const some_type mine = {1};


int main() {
  return mine[0] - 1;
}
