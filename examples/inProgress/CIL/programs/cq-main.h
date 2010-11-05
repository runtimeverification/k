
int main(n,args)               /* C REFERENCE MANUAL         */
int n;
char **args;
{
	static struct defs d0, *pd0;

	d0.flgs = 1;          /* These flags dictate            */
	d0.flgm = 1;          /*     the verbosity of           */
	d0.flgd = 1;          /*         the program.           */
	d0.flgl = 1;

	pd0 = &d0;

	d0.rrc = sec(pd0);
	d0.crc = d0.crc+d0.rrc;
	if(d0.flgs != 0) printf("Section %s returned %d.\n",d0.rfs,d0.rrc);
  
	if(d0.crc == 0) printf("\nNo errors detected.\n");
	else printf("\nFailed.\n");
	return 0;
}
