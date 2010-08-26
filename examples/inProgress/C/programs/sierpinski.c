/* Copyright (c) 2010 the authors listed at the following URL, and/or
the authors of referenced articles or incorporated external code:
http://en.literateprograms.org/Sierpinski_triangle_(C)?action=history&offset=20080102062902

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

Retrieved from: http://en.literateprograms.org/Sierpinski_triangle_(C)?oldid=11926
*/

#include<stdio.h>
#include<string.h>

char *apply_rules(char *new_sl, const char *sl, size_t width)
{
	int i;

	new_sl[0]=(sl[0] || sl[1]);
	new_sl[width-1]=(sl[width-2] || sl[width-1]);

	for(i=1; i<width-1; ++i) {
		char t1 = (sl[i-1] && sl[i] && sl[i+1]);
		char t2 = (!sl[i-1] && !sl[i] && !sl[i+1]);
		new_sl[i]=!(t1 || t2);
	}
	return new_sl;
}


void print_statelist(const char *sl, size_t width)
{
	int i;
	for(i=0; i<width; ++i) putchar(sl[i]?'@':' ');
	putchar('\n');
}


#define WIDTH 80
void run_and_display(size_t niters)
{
	char statelist1[WIDTH];
	char statelist2[WIDTH];
	char *statelist, *new_statelist;
	int i;

	memset(statelist1, 0, WIDTH);
	statelist1[WIDTH/2]=1;

	statelist=statelist1;
	new_statelist=statelist2;


	for(i=0; i<niters; ++i) {
		print_statelist(statelist, WIDTH);
		if((statelist=apply_rules(new_statelist, statelist, WIDTH))==statelist1)
			new_statelist=statelist2;
		else
			new_statelist=statelist1;
	}
}

int main()
{
	run_and_display(2);
	
	return 0;
}


