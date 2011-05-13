function main() {
	var x = 1;
	try { var x = 5; throw x; var y = x/0;}  // division by zero unreachable
	catch(y) {y = y + 2; write(y);}  // new y here, the one declared by catch
	write(x);
}
