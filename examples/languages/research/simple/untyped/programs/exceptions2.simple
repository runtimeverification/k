function main() {
	try
		foo();
	catch(e)
		write(e);  // should write 7
}

function foo() {
	try {
		throw 5;
		write(7);  // should not be written
	} catch(e) {
		throw e + 2; // throws 7
	}
	throw 1;     // should not be reached
}
