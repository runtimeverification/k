int step;

void hanoi(int t1, int t2, int t3, int n) {
    step++;
    if (n == 1) { return; }
    hanoi(t1, t3, t2, n-1);
    hanoi(t3, t2, t1, n-1);
}

int main(void) {
    int n = 4;
    hanoi(1, 2, 3, n);
	//printf("");
	return step;
}
