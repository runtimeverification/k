var x;

function f(y) {
	var t = 1;
	try{
		write(t);
		throw 5;
		write(8);  // not reachable
	} catch(p) {
		write(p+10);
	}
	for i = 1 to y do
		t = t*i;
	return t;
}

function main() {
	x = 5;
	write(f(x));
}