/* Copyright (c) 2010 the authors listed at the following URL, and/or
the authors of referenced articles or incorporated external code:
http://en.literateprograms.org/Base64_(C)?action=history&offset=20070707014726

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

Retrieved from: http://en.literateprograms.org/Base64_(C)?oldid=10650
*/

#include <stdio.h>
#include <string.h>

char b64[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
int nbytes[] = { 3, 1, 1, 2 };

void xlate(unsigned char *in, int phase)
{
    unsigned char out[3];
    out[0] = in[0] << 2 | in[1] >> 4;
    out[1] = in[1] << 4 | in[2] >> 2;
    out[2] = in[2] << 6 | in[3] >> 0;
	for (int i = 0; i < nbytes[phase]; i++){
		putchar(out[i]);
	}
	//fwrite(out, nbytes[phase], 1, stdout);
}


int main()
{
    int c, phase;
    unsigned char in[4];
    char *p;

    phase = 0;
	
	char* input = "TGl0ZXJhdGVQcm9ncmFtcw==";
	
    while((c = *input++) != 0) {
		//putchar(c);
        if(c == '=')    {
	    xlate(in,phase); 
	    break;
	}
	p = strchr(b64, c);
	if(p) {
	    in[phase] = p - b64;
	    phase = (phase + 1) % 4;
	    if(phase == 0)    {
	        xlate(in,phase); 
	        in[0]=in[1]=in[2]=in[3]=0;
	    }
	}

    }
    return 0;
}

