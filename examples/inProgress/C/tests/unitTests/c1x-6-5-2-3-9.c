union {
	struct {
		int alltypes;
	} n;
	struct {
		int type;
		int intnode;
	} ni;
	struct {
		int type;
		double doublenode;
	} nf;
} u;

int main(void){
	u.nf.type = 1;
	u.nf.doublenode = 3.14;
	if (u.n.alltypes == 1){
		if (u.nf.doublenode > 3){
			return 1;
		}
	}
	return 0;
}
