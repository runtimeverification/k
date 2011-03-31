function main() {
	var x = 1;
	spawn {x = x+1; rendezvous 1;}
	x = x+1;
	rendezvous 1;
	write(x);
}