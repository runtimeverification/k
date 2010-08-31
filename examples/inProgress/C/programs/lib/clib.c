#define NULL ((void *)0)
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
typedef unsigned long int size_t;
// nice public domain implementations at http://en.wikibooks.org/wiki/C_Programming/Strings

int getc(FILE *stream){
	return fgetc(stream);
}

char *strcpy(char *dest, const char *src) {
	unsigned i;
	for (i=0; src[i] != '\0'; ++i) {
		dest[i] = src[i];
	}
	dest[i] = '\0';
	return dest;
}

size_t strlen(const char * str) {
    const char *s;
    for (s = str; *s; ++s);
    return(s - str);
}

void* memset (void* dest, int value, size_t len) {
	unsigned char *ptr = (unsigned char*)dest;
	while (len-- > 0) {
		*ptr++ = value;
	}
	return dest;
}

void *memchr(const void *s, int c, size_t n) {
	const unsigned char *src = s;
	unsigned char uc = c;
	while (n-- != 0) {
		if (*src == uc) {
			return (void *) src;
		}
		src++;
	}
	return NULL;
}


int strcmp (const char * s1, const char * s2) {
    for(; *s1 == *s2; ++s1, ++s2)
        if(*s1 == 0)
            return 0;
    return *(unsigned char *)s1 < *(unsigned char *)s2 ? -1 : 1;
}

char *(strchr)(const char *s, int c) {
 /* Scan s for the character.  When this loop is finished,
	s will either point to the end of the string or the
	character we were looking for.  */
 while (*s != '\0' && *s != (char)c)
	 s++;
 return ( (*s == c) ? (char *) s : NULL );
}

int (strncmp)(const char *s1, const char *s2, size_t n) {
     unsigned char uc1, uc2;
     /* Nothing to compare?  Return zero.  */
     if (n == 0)
         return 0;
     /* Loop, comparing bytes.  */
     while (n-- > 0 && *s1 == *s2) {
         /* If we've run out of bytes or hit a null, return zero
            since we already know *s1 == *s2.  */
         if (n == 0 || *s1 == '\0')
             return 0;
         s1++;
         s2++;
     }
     uc1 = (*(unsigned char *) s1);
     uc2 = (*(unsigned char *) s2);
     return ((uc1 < uc2) ? -1 : (uc1 > uc2));
 }


char *(strrchr)(const char *s, int c) {
     const char *last = NULL;
     /* If the character we're looking for is the terminating null,
        we just need to look for that character as there's only one
        of them in the string.  */
     if (c == '\0')
         return strchr(s, c);
     /* Loop through, finding the last match before hitting NULL.  */
     while ((s = strchr(s, c)) != NULL) {
         last = s;
         s++;
     }
     return (char *) last;
 }



// from http://www.danielvik.com/2010/02/fast-memcpy-in-c.html
// by Daniel Vik
void* memcpy(void* dest, const void* src, size_t count) {
	char* dst8 = (char*)dest;
	char* src8 = (char*)src;

	while (count--) {
		*dst8++ = *src8++;
	}
	return dest;
}

// this is public domain
int memcmp(const void *s1, const void *s2, size_t n) {
	const unsigned char *us1 = (const unsigned char *) s1;
	const unsigned char *us2 = (const unsigned char *) s2;
	while (n-- != 0) {
		if (*us1 != *us2) {
			return (*us1 < *us2) ? -1 : +1;
		}
		us1++;
		us2++;
	}
	return 0;
}


char * strcat(char *dest, const char *src){
    strcpy(dest + strlen(dest), src);
    return dest;
}

int puts(const char * str){
	return printf("%s\n", str);
}

int fslPutc(char c, int handle);
int fslOpenFile(const char* filename, int handle);
int fslCloseFile(int handle);
int fslFGetC(int handle, unsigned long long int offset);
int fsl_next_fd = 3;

int putc (char c, FILE* stream) {
	return fslPutc(c, stream->handle);
}


FILE stdin_file = {0, 0, 0};
FILE stdout_file = {0, 1, 0};
FILE stderr_file = {0, 2, 0};
FILE* stdin = &stdin_file;
FILE* stdout = &stdout_file;
FILE* stderr = &stderr_file;
FILE* fopen(const char *filename, const char *mode){
	int nextHandle = fsl_next_fd++;
	int retval = fslOpenFile(filename, nextHandle);
	if (retval) {
		return NULL;
	}
	
	FILE* newFile = (FILE*)malloc(sizeof(FILE));
	newFile->offset = 0;
	newFile->handle = nextHandle;
	
	return newFile;
}

int fclose(FILE* stream){
	int retval = fslCloseFile(stream->handle);
	if (retval) {
		return EOF;
	}
	free(stream);
	
	return 0;
}

int feof ( FILE * stream ) {
	return stream->eof;
}

int fgetc(FILE* stream){
	int retval = fslFGetC(stream->handle, stream->offset);
	if (retval >= 0) {
		stream->offset++;
	} else {
		stream->eof = 1;
	}
	//printf("read %x\n", retval);
	return retval;
}

char* fgets (char* restrict str, int size, FILE* restrict stream){
	if (size < 2){ return NULL; }
	int i = 0;
	while (i < size - 1){
		int oneChar = fgetc(stream);
		if (oneChar == EOF) {
			if (i == 0) {
				return NULL;
			} else {
				break;
			}
		}
		str[i] = oneChar;
		if (oneChar == '\n') {
			break;
		}
		
		i++;
	}
	str[i + 1] = '\0';
	return str;
}


int atoi(const char *c) {
	int res = 0;
	while (*c >= '0' && *c <= '9')
		res = res * 10 + *c++ - '0';
	return res;
}

// math.h
int abs( int num ){
	if (num >= 0) {
		return num;
	} else {
		return -num;
	}
}
double fabs( double num ){
	if (num >= 0.0) {
		return num;
	} else {
		return -num;
	}
}
double pow(double x, double y) {
	if (x == 0 && y == 0) {
		return 1; // this is what gcc seems to do
	}
	if (x == 0 && y != 0) {
		return 0;
	}
	if (y == 0 && x != 0) {
		return 1;
	}
	if (x < 0) {
		if (y/1.00 == (int)y) {
			if ((int)y % 2) {
				return -exp(y*log(-x));
			} else {
				return exp(y*log(-x));
			}
		}
	}
	return exp(y*log(x));
	// 	+ 1e-6;
}
