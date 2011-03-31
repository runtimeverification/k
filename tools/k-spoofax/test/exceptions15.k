function main() {
	try {
		1;
		try {
			2;
		} catch(a) {
			write(2);
		}
		throw 1;
	} catch(b) {
		write(1);
	}
}