
typedef
int
(__stdcall *LPOVERLAPPED_COMPLETION_ROUTINE)(int x);


int __stdcall AsynchRead(int x) {
  return x + 5;
}


int
__stdcall
ReadFileEx(int x1, 
           LPOVERLAPPED_COMPLETION_ROUTINE lpCompletionRoutine) {

  return lpCompletionRoutine(x1) + 6;
}


int main() {
  return -11 + ReadFileEx(0,
                          (int (__stdcall *)(int x))&AsynchRead);
}
