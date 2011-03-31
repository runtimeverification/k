var x, y, z;

function g() {
	throw 15;
}

function f() {
	g();
}

function main() {
	x = 5;
	y = 10;

	try {
		f();
	} catch(y) {
		write(y);
	}
	write(x);
	write(y);
}