var v[100];

function bubbleSort(n) {
	var t;
	for x = 0 to n - 1 do
		for y = 0 to n - 2 do
			if v[y] > v[y+1] then {
				t = v[y+1];
				v[y+1] = v[y];
				v[y] = t;
			}
}

function main() {
	var x = read();
	for y = 0 to (x - 1) do {
		v[y] = read();
		write(v[y]);
	}
	bubbleSort(x);
	for y = 0 to (x - 1) do
		write(v[y]);
}
