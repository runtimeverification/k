var x;

function f(y) {
	var t = 1;
	try{
		write(t);
		write(8);
	} catch(p) {
		write(p+10);  // not reachable
	}
	for i = 1 to y do
		t = t*i;
	return t;
}

function main() {
	x = 5;
	write(f(x));
}