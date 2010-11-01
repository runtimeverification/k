// string.h
#define NULL ((void *)0)
typedef unsigned long int size_t; // this needs to correspond to cfg:sizeut
size_t strlen(char *str);
int strcmp(const char *str1, const char *str2);
char* strcpy(char* s1, const char* s2);
char* strncpy(char * restrict dest, const char * restrict src, size_t n);
char* strcat(char* dest, const char* src);
char* strchr(const char *s, int c);
void * memset ( void * ptr, int value, size_t num );
void * memcpy ( void * destination, const void * source, size_t num );
int memcmp(const void *s1, const void *s2, size_t n);
void *memchr(const void *s, int c, size_t n);
char * strrchr ( const char *, int );
int strncmp(const char *s1, const char *s2, size_t n);
