var x[10];

function init(n) {
	for i = 0 to n - 1 do
		x[i] = (n - i) + 100;
}

function printAll(n) {
	for i = 0 to n - 1 do
		write(x[i]);
}

function main() {
	var n=10;
	init(n);
	printAll(n);
	for i = 1 to n - 1 do {
		var j = i - 1, v = x[i];
		while (j >= 0 and ((x[j]) > v)) do {
			x[j + 1] = x[j];
			j = j - 1;
		}
		x[j+1] = v;
	}
	printAll(n);
}
