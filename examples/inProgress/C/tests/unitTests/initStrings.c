int main (void){
    char s1[] = "x";
	char s2[2] = "";
	if (s1[0] != 'x') { return 1; }
	if (s1[1] != 0) { return 2; }
	if (s2[0] != 0) { return 3; }
	if (s2[1] != 0) { return 4; }
	return 0;
}
