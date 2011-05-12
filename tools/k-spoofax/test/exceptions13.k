function main() {
	try {
		throw 4;
	} catch (e) {
		write ( e );
	}
	write ( 42 );
}
