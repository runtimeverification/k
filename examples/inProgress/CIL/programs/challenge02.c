struct {int x[5];} s;
int main() {
	char* p = (char*)&s;
	*((int*)(p + sizeof(int))) = 5;
	return s.x[1];
}
// should return 5
