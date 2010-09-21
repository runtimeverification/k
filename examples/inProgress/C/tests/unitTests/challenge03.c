typedef struct { char a[2]; } s;
union { s a[2]; } u = {1, 2, 3, 4};
int main() {
	char* p = (char*)&u;
	return p[0] + p[1] + p[sizeof(s) + 0] + p[sizeof(s) + 1];
}
// should return 10
