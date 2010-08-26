// gcc and Elsa handle this but Cil can't handle this:
void
(*posix_signal(sig_num, action))()
    int sig_num;
    void (*action)();
{
}

// These are ok in all three tools.  The fun thing is that I guessed // these two would go through Cil before I tried them. :-)
void posix_signal2(sig_num, action)
    int sig_num;
    void (*action)();
{
}

void
(*posix_signal3(int sig_num, void (*action)() ))() {
  return 0;
}

int main() {
  return 0;
}

