var i, j;

function main() {
	i = 0;
	while (++i <= 3) do {
		write(i);
	}
	try ({i = 10; write(i);}) catch(j) ({i = 20;write(i);})
	i = 15;
	write(i);
}