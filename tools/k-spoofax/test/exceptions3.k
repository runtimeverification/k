function main() {
	var x = 1;
	try { x = x + 1; throw x; var y = x/0;}     // division by zero unreachable
	catch(y) {x = x+1;}
	write(x);
}