
void g();
void h();

int main(int argc, char ** argv) {
  h();
  return 0;
}

void h() {
  return(g());
}

void g() {
  return;
}
