// based on code from http://stackoverflow.com/questions/252552/unions-in-c (comment by Adam Rosenfield)

#include <stdio.h>

//enum TYPE { INTS, FLOATS, DOUBLE };
struct S {
	//enum TYPE s_type;
	int s_type;
	union {
		int s_ints[2];
		float s_floats[2];
		double s_double;
	} u;
};

void do_something(struct S *s) {
	switch(s->s_type) {
		case 0:  // do something with s->s_ints
			printf("This S has type INTS.\n");
			printf("%d, %d\n", s->u.s_ints[0], s->u.s_ints[1]);
			break;

		case 1:  // do something with s->s_floats
			printf("This S has type FLOATS.\n");
			printf("VOLATILE %f, %f\n", s->u.s_floats[0], s->u.s_floats[1]);
			if (s->u.s_floats[0] != - s->u.s_floats[1]){
				printf("s->u.s_floats[0] != - s->u.s_floats[1]: %f, %f\n",s->u.s_floats[0], - s->u.s_floats[1]);
			}
			break;

		case 2:  // do something with s->s_double
			printf("This S has type DOUBLE.\n");
			printf("VOLATILE %f\n", s->u.s_double);
			if (s->u.s_double > 1.57080 || s->u.s_double < 1.57079){
				printf("s->u.s_double is off: %f\n", s->u.s_double);
			}
			break;
	}
}

int main(void){
	struct S esses[3];
	//printf("sizeof(esses)=%d\n", sizeof(esses));
	//printf("sizeof(esses[0])=%d\n", sizeof(esses[0]));
	int numEsses = sizeof(esses)/sizeof(esses[0]);
	//printf("numEsses=%d\n", numEsses);
	//printf("&esses[0]=%d, &esses[1]=%d, &esses[2]=%d\n", &esses[0], &esses[1], &esses[2]);
	esses[0].s_type = 0;
	esses[0].u.s_ints[0] = 2123456789;
	esses[0].u.s_ints[1] = -2123456789;
	esses[1].s_type = 1;
	esses[1].u.s_floats[0] = 3.14159265;
	esses[1].u.s_floats[1] = -3.14159265;
	esses[2].s_type = 2;
	esses[2].u.s_double = 3.14159265358979 / 2.0;
	struct S newStruct = esses[1];

	for (int i = 0; i < numEsses; i++){
		do_something(&esses[i]);
	}
	return 0;
}
