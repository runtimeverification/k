struct S1 {
	union {
		int a;
		float b;
	};
} s;

int main(void){
	s.a = 5;
	(&s)->a = s.a + 2;
	return (&s)->a;
}
