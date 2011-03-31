function main() {
	var x = 1;
	spawn {acquire 1; x = x+1; release 1; rendezvous 1;}
	acquire 1;
	x = x+1;
	release 1;
	rendezvous 1;
	write(x);
}