var x;
function main() {
	var factorialOf = 5;
	x = 1;
	for i = 1 to factorialOf do {
		spawn multX(i);
	}
	for i = 1 to factorialOf do
		rendezvous i;
	write(x);
}

function multX(v) {
	acquire 0;
	x = x*v;
	release 0;
	rendezvous v;
}
