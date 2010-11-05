#define NULL 0
typedef unsigned long int size_t; // this needs to correspond to cfg:sizeut

// from http://tigcc.ticalc.org/doc/stdio.html#FILE
enum FileFlags {_F_READ = 0x0001, _F_WRIT = 0x0002, _F_RDWR = 0x0003, _F_ERR = 0x0010, _F_EOF = 0x0020, _F_BIN = 0x0040};
typedef struct {
	unsigned long long int offset;
	//char* fpos; /* Current position of file pointer (absolute address) */
	//void* base; /* Pointer to the base of the file */
	unsigned short handle; /* File handle */
	unsigned char eof;
	//short flags; /* Flags (see FileFlags) */
	//short unget; /* 1-byte buffer for ungetc (b15=1 if non-empty) */
	//unsigned long alloc; /* Number of currently allocated bytes for the file */
	//unsigned short buffincrement; /* Number of bytes allocated at once */
} FILE;




extern FILE stdin_file;
extern FILE stdout_file;
extern FILE stderr_file;

extern FILE* stdin;
extern FILE* stdout;
extern FILE* stderr;


// stdio.h
#define EOF -1
int putchar ( int character );
int getchar ( void );
int printf(const char *format, ...);
int puts (const char * str);

//int getc(FILE *stream);
int getc(FILE *stream);
int feof ( FILE * stream );
FILE* fopen(const char *filename, const char *mode);
int fclose(FILE *stream);
int fgetc(FILE *stream);
char* fgets (char* restrict str, int size, FILE* restrict stream);



