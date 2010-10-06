/* Copyright 2002 Free Software Foundation, Inc.

   Tests correct signedness of operations on bitfields; in particular
   that integer promotions are done correctly, including the case when
   casts are present.

   The C front end was eliding the cast of an unsigned bitfield to
   unsigned as a no-op, when in fact it forces a conversion to a
   full-width unsigned int. (At the time of writing, the C++ front end
   has a different bug; it erroneously promotes the uncast unsigned
   bitfield to an unsigned int).

   Source: Neil Booth, 25 Jan 2002, based on PR 3325 (and 3326, which
   is a different manifestation of the same bug).
*/
#include <stdio.h>

int main(void) {
	struct x { signed int i : 7; unsigned int u : 7; } bit;

	unsigned int u;
	int i;
	unsigned int unsigned_result = -13U % 61;
	int signed_result = -13 % 61;

	bit.u = 61, u = 61; 
	bit.i = -13, i = -13;

	printf("i=%d, u=%d\n", i, u);
	printf("bit.i=%d, bit.u=%d\n", bit.i, bit.u);
	printf("unsigned_result=%d, signed_result=%d\n", unsigned_result, signed_result);
	
	printf("i %% u = %d\n", i % u);
	if (i % u != unsigned_result) {
		printf("i %% u != unsigned_result\n");
	}
	
	printf("i %% (unsigned int) u = %d\n", i % (unsigned int) u);
	if (i % (unsigned int) u != unsigned_result) {
		printf("i %% (unsigned int) u != unsigned_result\n");
	}

	/* Somewhat counter-intuitively, bit.u is promoted to an int, making the operands and result an int.  */
	printf("i %% bit.u = %d\n", i % bit.u);
	if (i % bit.u != signed_result) {
		printf("i %% bit.u != signed_result\n");
	}

	printf("bit.i %% bit.u = %d\n", bit.i % bit.u);
	if (bit.i % bit.u != signed_result) {
		printf("bit.i %% bit.u != signed_result\n");
	}

	/* But with a cast to unsigned int, the unsigned int is promoted to itself as a no-op, and the operands and result are unsigned. */
	printf("i %% (unsigned int) bit.u = %d\n", i % (unsigned int) bit.u);
	if (i % (unsigned int) bit.u != unsigned_result) {
		printf("i %% (unsigned int) bit.u != unsigned_result\n");
	}

	printf("bit.i %% (unsigned int) bit.u = %d\n", bit.i % (unsigned int) bit.u);
	if (bit.i % (unsigned int) bit.u != unsigned_result) {
		printf("bit.i %% (unsigned int) bit.u != unsigned_result\n");
	}

  return 0;
}
