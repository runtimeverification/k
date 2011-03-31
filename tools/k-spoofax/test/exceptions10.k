var x;

function main() {
	x = 5;
	try {
		throw 3;
		write(x);
	} catch(y) {
		write(y);
	}
}