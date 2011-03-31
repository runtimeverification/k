function init(x,n) {
	for i = 0 to n - 1 do
	x[i] = (n-i) + 100;
}

function printAll(x,n) {
	for i = 0 to n - 1 do
		write(x[i]);
}

function main() {
	var x[100], n = 30;
	init(x,n);
	printAll(x,n);
	write(-1);
	for i = 1 to n - 1 do {
		var j = i - 1, v = x[i];
		while (j >= 0) do {
			if x[j] > v then x[j+1] = x[j];
			j = j - 1;
		}
		x[j+1] = v;
	}
	printAll(x,n);
}