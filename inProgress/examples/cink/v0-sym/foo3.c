    int f(int n) {
       int x;
       x = n;
       unlock();
       return x + 1;
    }
    int main() {
       int i;
       int n;
       lock();
       scanf("%d", &n);
       if (n > 0) {
          f(n);
       }
       unlock();
    }
