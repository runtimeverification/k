# 1 "cof.c"
# 1 "/home/scott/wrk/safec/cil/lib/fixup.h" 1
 

# 21 "/home/scott/wrk/safec/cil/lib/fixup.h"



 








# 55 "/home/scott/wrk/safec/cil/lib/fixup.h"


































 





void exit(int);



 

#pragma ccuredalloc("malloc", nozero, sizein(1))
#pragma ccuredalloc("alloca", nozero, sizein(1))
#pragma ccuredalloc("calloc", zero, sizemul(1,2))

#pragma ccuredvararg("printf", printf(1))
#pragma ccuredvararg("fprintf", printf(2))
#pragma ccuredvararg("sprintf", printf(2))
#pragma ccuredvararg("snprintf", printf(3))

#pragma ccuredexported("main")



 

# 1 "cof.c" 2
# 1 "espresso.h" 1
 



# 1 "port.h" 1







# 19 "port.h"


 





 






      
typedef long int32;
typedef int int16;




# 57 "port.h"






# 1 "/usr/include/stdio.h" 1 3
 

















 







# 1 "/usr/include/features.h" 1 3
 




















 


























































 



















 





 



 







 
# 137 "/usr/include/features.h" 3


 









 





 



























# 195 "/usr/include/features.h" 3


































 



 








 




 

# 1 "/usr/include/sys/cdefs.h" 1 3
 




















 




 





 








 




# 71 "/usr/include/sys/cdefs.h" 3


 







 



# 103 "/usr/include/sys/cdefs.h" 3



 








 















 








 








 









 







# 249 "/usr/include/features.h" 2 3


 








 





 

 








# 1 "/usr/include/gnu/stubs.h" 1 3
 






































# 277 "/usr/include/features.h" 2 3




# 27 "/usr/include/stdio.h" 2 3


 



# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 1 3






 


# 19 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3



 


 





 


# 61 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 





 


















 





 

 

# 131 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 


































typedef unsigned int size_t;






















 




 

# 271 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


# 283 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 

# 317 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3




 





















# 33 "/usr/include/stdio.h" 2 3





# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stdarg.h" 1 3
 





























































 






typedef void *__gnuc_va_list;



 

# 116 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stdarg.h" 3



















# 202 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stdarg.h" 3




# 38 "/usr/include/stdio.h" 2 3


# 1 "/usr/include/bits/types.h" 1 3
 

















 









# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 1 3






 


# 19 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3



 


 





 


# 61 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 





 


















 





 

 

# 131 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 


# 188 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3





 




 

# 271 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


# 283 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 

# 317 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3




 





















# 29 "/usr/include/bits/types.h" 2 3


 
typedef unsigned char __u_char;
typedef unsigned short __u_short;
typedef unsigned int __u_int;
typedef unsigned long __u_long;

__extension__ typedef unsigned long long int __u_quad_t;
__extension__ typedef long long int __quad_t;
# 48 "/usr/include/bits/types.h" 3

typedef signed char __int8_t;
typedef unsigned char __uint8_t;
typedef signed short int __int16_t;
typedef unsigned short int __uint16_t;
typedef signed int __int32_t;
typedef unsigned int __uint32_t;

__extension__ typedef signed long long int __int64_t;
__extension__ typedef unsigned long long int __uint64_t;

typedef __quad_t *__qaddr_t;

typedef __u_quad_t __dev_t;		 
typedef __u_int __uid_t;		 
typedef __u_int __gid_t;		 
typedef __u_long __ino_t;		 
typedef __u_int __mode_t;		 
typedef __u_int __nlink_t; 		 
typedef long int __off_t;		 
typedef __quad_t __loff_t;		 
typedef int __pid_t;			 
typedef int __ssize_t;			 
typedef long int __rlim_t;		 
typedef __quad_t __rlim64_t;		 
typedef __u_int __id_t;			 

typedef struct
  {
    int __val[2];
  } __fsid_t;				 

 
typedef int __daddr_t;			 
typedef char *__caddr_t;
typedef long int __time_t;
typedef long int __swblk_t;		 

typedef long int __clock_t;

 
typedef unsigned long int __fd_mask;

 


 




 
typedef struct
  {
     





    __fd_mask __fds_bits[1024  / (8 * sizeof (__fd_mask)) ];


  } __fd_set;


typedef int __key_t;

 
typedef unsigned short int __ipc_pid_t;


 

 
typedef long int __blkcnt_t;
typedef __quad_t __blkcnt64_t;

 
typedef __u_long __fsblkcnt_t;
typedef __u_quad_t __fsblkcnt64_t;

 
typedef __u_long __fsfilcnt_t;
typedef __u_quad_t __fsfilcnt64_t;

 
typedef __u_long __ino64_t;

 
typedef __loff_t __off64_t;

 
typedef int __t_scalar_t;
typedef unsigned int __t_uscalar_t;

 
typedef int __intptr_t;


 





# 40 "/usr/include/stdio.h" 2 3







 
typedef struct _IO_FILE FILE;








# 1 "/usr/include/libio.h" 1 3
 




























# 1 "/usr/include/_G_config.h" 1 3
 





 






# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 1 3






 


# 19 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3



 


 





 


# 61 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 





 


















 





 

 

# 131 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 


# 188 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3





 




 





























 


























typedef long int wchar_t;
























typedef unsigned int  wint_t;




 

 

# 317 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3




 





















# 14 "/usr/include/_G_config.h" 2 3





















typedef int _G_int16_t __attribute__ ((__mode__ (__HI__)));
typedef int _G_int32_t __attribute__ ((__mode__ (__SI__)));
typedef unsigned int _G_uint16_t __attribute__ ((__mode__ (__HI__)));
typedef unsigned int _G_uint32_t __attribute__ ((__mode__ (__SI__)));




 


















 




 














# 30 "/usr/include/libio.h" 2 3
















 

# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stdarg.h" 1 3
 





























































 










 

# 116 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stdarg.h" 3



















# 202 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stdarg.h" 3




# 48 "/usr/include/libio.h" 2 3







# 67 "/usr/include/libio.h" 3


 

















# 98 "/usr/include/libio.h" 3











 
























 



















struct _IO_jump_t;  struct _IO_FILE;

 







typedef void _IO_lock_t;



 

struct _IO_marker {
  struct _IO_marker *_next;
  struct _IO_FILE *_sbuf;
   

   
  int _pos;
# 186 "/usr/include/libio.h" 3

};

struct _IO_FILE {
  int _flags;		 


   
   
  char* _IO_read_ptr;	 
  char* _IO_read_end;	 
  char* _IO_read_base;	 
  char* _IO_write_base;	 
  char* _IO_write_ptr;	 
  char* _IO_write_end;	 
  char* _IO_buf_base;	 
  char* _IO_buf_end;	 
   
  char *_IO_save_base;  
  char *_IO_backup_base;   
  char *_IO_save_end;  

  struct _IO_marker *_markers;

  struct _IO_FILE *_chain;

  int _fileno;
  int _blksize;
  __off_t   _old_offset;  


   
  unsigned short _cur_column;
  signed char _vtable_offset;
  char _shortbuf[1];

   

  _IO_lock_t *_lock;








  __off64_t   _offset;
   
  int _unused2[16];

};


typedef struct _IO_FILE _IO_FILE;


struct _IO_FILE_plus;
extern struct _IO_FILE_plus _IO_2_1_stdin_;
extern struct _IO_FILE_plus _IO_2_1_stdout_;
extern struct _IO_FILE_plus _IO_2_1_stderr_;











 

 

typedef __ssize_t __io_read_fn  (void *  __cookie, char *__buf,
				       size_t __nbytes)  ;

 





typedef __ssize_t __io_write_fn  (void *  __cookie, __const char *__buf,
				      size_t __n)  ;

 





typedef int __io_seek_fn  (void *  __cookie, __off_t   __pos, int __w)  ;

 
typedef int __io_close_fn  (void *  __cookie)  ;


# 311 "/usr/include/libio.h" 3







extern int __underflow  (_IO_FILE *)    ;
extern int __uflow  (_IO_FILE *)    ;
extern int __overflow  (_IO_FILE *, int)    ;
















extern int _IO_getc  (_IO_FILE *__fp)    ;
extern int _IO_putc  (int __c, _IO_FILE *__fp)    ;
extern int _IO_feof  (_IO_FILE *__fp)    ;
extern int _IO_ferror  (_IO_FILE *__fp)    ;

extern int _IO_peekc_locked  (_IO_FILE *__fp)    ;

 



extern void _IO_flockfile  (_IO_FILE *)    ;
extern void _IO_funlockfile  (_IO_FILE *)    ;
extern int _IO_ftrylockfile  (_IO_FILE *)    ;












extern int _IO_vfscanf  (_IO_FILE *  , const char *  ,
			     __gnuc_va_list , int *  )    ;
extern int _IO_vfprintf  (_IO_FILE *  , const char *  ,
			      __gnuc_va_list )    ;
extern __ssize_t   _IO_padn  (_IO_FILE *, int, __ssize_t  )    ;
extern size_t   _IO_sgetn  (_IO_FILE *, void *, size_t  )    ;

extern __off64_t   _IO_seekoff  (_IO_FILE *, __off64_t  , int, int)    ;
extern __off64_t   _IO_seekpos  (_IO_FILE *, __off64_t  , int)    ;

extern void _IO_free_backup_area  (_IO_FILE *)    ;






# 57 "/usr/include/stdio.h" 2 3


 

typedef __off_t  fpos_t;







 





 





 






 







 




 








# 1 "/usr/include/bits/stdio_lim.h" 1 3
 




































# 110 "/usr/include/stdio.h" 2 3



 
extern FILE *stdin;		 
extern FILE *stdout;		 
extern FILE *stderr;		 


 
extern int remove  (__const char *__filename)    ;
 
extern int rename  (__const char *__old, __const char *__new)    ;


 

extern FILE *tmpfile  (void)    ;










 
extern char *tmpnam  (char *__s)    ;


 

extern char *tmpnam_r  (char *__s)    ;




 






extern char *tempnam  (__const char *__dir, __const char *__pfx)    ;



 
extern int fclose  (FILE *__stream)    ;
 
extern int fflush  (FILE *__stream)    ;


 
extern int fflush_unlocked  (FILE *__stream)    ;









 
extern FILE *fopen  (__const char *   __filename,
			 __const char *   __modes)    ;
 
extern FILE *freopen  (__const char *   __filename,
			   __const char *   __modes,
			   FILE *   __stream)    ;
# 197 "/usr/include/stdio.h" 3










 
extern FILE *fdopen  (int __fd, __const char *__modes)    ;


# 223 "/usr/include/stdio.h" 3



 

extern void setbuf  (FILE *   __stream, char *   __buf)    ;
 


extern int setvbuf  (FILE *   __stream, char *   __buf,
			 int __modes, size_t __n)    ;


 

extern void setbuffer  (FILE *   __stream, char *   __buf,
			    size_t __size)    ;

 
extern void setlinebuf  (FILE *__stream)    ;



 
extern int fprintf  (FILE *   __stream,
			 __const char *   __format, ...)    ;
 
extern int printf  (__const char *   __format, ...)    ;
 
extern int sprintf  (char *   __s,
			 __const char *   __format, ...)    ;

 
extern int vfprintf  (FILE *   __s,
			  __const char *   __format,
			  __gnuc_va_list  __arg)    ;
 
extern int vprintf  (__const char *   __format,
			 __gnuc_va_list  __arg)    ;
 
extern int vsprintf  (char *   __s,
			  __const char *   __format,
			  __gnuc_va_list  __arg)    ;


 
extern int snprintf  (char *   __s, size_t __maxlen,
			  __const char *   __format, ...)    
     __attribute__ ((__format__ (__printf__, 3, 4)));

extern int __vsnprintf  (char *   __s, size_t __maxlen,
			     __const char *   __format,
			     __gnuc_va_list  __arg)    
     __attribute__ ((__format__ (__printf__, 3, 0)));
extern int vsnprintf  (char *   __s, size_t __maxlen,
			   __const char *   __format,
			   __gnuc_va_list  __arg)    
     __attribute__ ((__format__ (__printf__, 3, 0)));


# 302 "/usr/include/stdio.h" 3



 
extern int fscanf  (FILE *   __stream,
			__const char *   __format, ...)    ;
 
extern int scanf  (__const char *   __format, ...)    ;
 
extern int sscanf  (__const char *   __s,
			__const char *   __format, ...)    ;

# 330 "/usr/include/stdio.h" 3



 
extern int fgetc  (FILE *__stream)    ;
extern int getc  (FILE *__stream)    ;

 
extern int getchar  (void)    ;

 




 
extern int getc_unlocked  (FILE *__stream)    ;
extern int getchar_unlocked  (void)    ;



 
extern int fgetc_unlocked  (FILE *__stream)    ;



 
extern int fputc  (int __c, FILE *__stream)    ;
extern int putc  (int __c, FILE *__stream)    ;

 
extern int putchar  (int __c)    ;

 




 
extern int fputc_unlocked  (int __c, FILE *__stream)    ;



 
extern int putc_unlocked  (int __c, FILE *__stream)    ;
extern int putchar_unlocked  (int __c)    ;




 
extern int getw  (FILE *__stream)    ;

 
extern int putw  (int __w, FILE *__stream)    ;



 
extern char *fgets  (char *   __s, int __n,
			 FILE *   __stream)    ;







 

extern char *gets  (char *__s)    ;


# 420 "/usr/include/stdio.h" 3



 
extern int fputs  (__const char *   __s,
		       FILE *   __stream)    ;







 
extern int puts  (__const char *__s)    ;


 
extern int ungetc  (int __c, FILE *__stream)    ;


 
extern size_t fread  (void *   __ptr, size_t __size,
			  size_t __n, FILE *   __stream)    ;
 
extern size_t fwrite  (__const void *   __ptr, size_t __size,
			   size_t __n, FILE *   __s)    ;


 
extern size_t fread_unlocked  (void *   __ptr, size_t __size,
				   size_t __n, FILE *   __stream)    ;
extern size_t fwrite_unlocked  (__const void *   __ptr,
				    size_t __size, size_t __n,
				    FILE *   __stream)    ;



 
extern int fseek  (FILE *__stream, long int __off, int __whence)    ;
 
extern long int ftell  (FILE *__stream)    ;
 
extern void rewind  (FILE *__stream)    ;

 




 


typedef __off_t off_t;




















 
extern int fgetpos  (FILE *   __stream,
			 fpos_t *   __pos)    ;
 
extern int fsetpos  (FILE *__stream, __const fpos_t *__pos)    ;
# 519 "/usr/include/stdio.h" 3


# 529 "/usr/include/stdio.h" 3


 
extern void clearerr  (FILE *__stream)    ;
 
extern int feof  (FILE *__stream)    ;
 
extern int ferror  (FILE *__stream)    ;


 
extern void clearerr_unlocked  (FILE *__stream)    ;
extern int feof_unlocked  (FILE *__stream)    ;
extern int ferror_unlocked  (FILE *__stream)    ;



 
extern void perror  (__const char *__s)    ;

 


extern int sys_nerr;
extern __const char *__const sys_errlist[];








 
extern int fileno  (FILE *__stream)    ;



 
extern int fileno_unlocked  (FILE *__stream)    ;





 
extern FILE *popen  (__const char *__command, __const char *__modes)    ;

 
extern int pclose  (FILE *__stream)    ;




 
extern char *ctermid  (char *__s)    ;









# 603 "/usr/include/stdio.h" 3




 

 
extern void flockfile  (FILE *__stream)    ;

 

extern int ftrylockfile  (FILE *__stream)    ;

 
extern void funlockfile  (FILE *__stream)    ;










 





 




# 63 "port.h" 2

# 1 "/usr/include/ctype.h" 1 3
 

















 









 


 







# 1 "/usr/include/endian.h" 1 3
 






















 









 
# 1 "/usr/include/bits/endian.h" 1 3
 






# 35 "/usr/include/endian.h" 2 3


 













# 40 "/usr/include/ctype.h" 2 3







enum
{
  _ISupper = (( 0 ) < 8 ? ((1 << ( 0 )) << 8) : ((1 << ( 0 )) >> 8)) ,	 
  _ISlower = (( 1 ) < 8 ? ((1 << ( 1 )) << 8) : ((1 << ( 1 )) >> 8)) ,	 
  _ISalpha = (( 2 ) < 8 ? ((1 << ( 2 )) << 8) : ((1 << ( 2 )) >> 8)) ,	 
  _ISdigit = (( 3 ) < 8 ? ((1 << ( 3 )) << 8) : ((1 << ( 3 )) >> 8)) ,	 
  _ISxdigit = (( 4 ) < 8 ? ((1 << ( 4 )) << 8) : ((1 << ( 4 )) >> 8)) ,	 
  _ISspace = (( 5 ) < 8 ? ((1 << ( 5 )) << 8) : ((1 << ( 5 )) >> 8)) ,	 
  _ISprint = (( 6 ) < 8 ? ((1 << ( 6 )) << 8) : ((1 << ( 6 )) >> 8)) ,	 
  _ISgraph = (( 7 ) < 8 ? ((1 << ( 7 )) << 8) : ((1 << ( 7 )) >> 8)) ,	 
  _ISblank = (( 8 ) < 8 ? ((1 << ( 8 )) << 8) : ((1 << ( 8 )) >> 8)) ,	 
  _IScntrl = (( 9 ) < 8 ? ((1 << ( 9 )) << 8) : ((1 << ( 9 )) >> 8)) ,	 
  _ISpunct = (( 10 ) < 8 ? ((1 << ( 10 )) << 8) : ((1 << ( 10 )) >> 8)) ,	 
  _ISalnum = (( 11 ) < 8 ? ((1 << ( 11 )) << 8) : ((1 << ( 11 )) >> 8)) 	 
};


 










extern __const unsigned short int *__ctype_b;	 
extern __const __int32_t *__ctype_tolower;  
extern __const __int32_t *__ctype_toupper;  









 



extern int  isalnum   (int)     ;
extern int  isalpha   (int)     ;
extern int  iscntrl   (int)     ;
extern int  isdigit   (int)     ;
extern int  islower   (int)     ;
extern int  isgraph   (int)     ;
extern int  isprint   (int)     ;
extern int  ispunct   (int)     ;
extern int  isspace   (int)     ;
extern int  isupper   (int)     ;
extern int  isxdigit   (int)     ;






 
extern int tolower  (int __c)    ;

 
extern int toupper  (int __c)    ;




 

extern int isascii  (int __c)    ;

 

extern int toascii  (int __c)    ;




 

extern int  _toupper   (int)     ;
extern int  _tolower   (int)     ;



















# 164 "/usr/include/ctype.h" 3


# 186 "/usr/include/ctype.h" 3













# 273 "/usr/include/ctype.h" 3


 


# 64 "port.h" 2

# 1 "/usr/include/sys/types.h" 1 3
 

















 








 




typedef __u_char u_char;
typedef __u_short u_short;
typedef __u_int u_int;
typedef __u_long u_long;
typedef __quad_t quad_t;
typedef __u_quad_t u_quad_t;
typedef __fsid_t fsid_t;


typedef __loff_t loff_t;



typedef __ino_t ino_t;










typedef __dev_t dev_t;




typedef __gid_t gid_t;




typedef __mode_t mode_t;




typedef __nlink_t nlink_t;




typedef __uid_t uid_t;

















typedef __pid_t pid_t;




typedef __id_t id_t;



typedef __ssize_t ssize_t;




typedef __daddr_t daddr_t;
typedef __caddr_t caddr_t;



typedef __key_t key_t;






# 1 "/usr/include/time.h" 1 3
 

















 














# 51 "/usr/include/time.h" 3



# 62 "/usr/include/time.h" 3








 
typedef __time_t time_t;





# 89 "/usr/include/time.h" 3




# 279 "/usr/include/time.h" 3



# 121 "/usr/include/sys/types.h" 2 3



# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 1 3






 


# 19 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3



 


 





 


# 61 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 





 


















 





 

 

# 131 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 


# 188 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3





 




 

# 271 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


# 283 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 

# 317 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3




 





















# 124 "/usr/include/sys/types.h" 2 3



 
typedef unsigned long int ulong;
typedef unsigned short int ushort;
typedef unsigned int uint;


 

# 158 "/usr/include/sys/types.h" 3


 







typedef int int8_t __attribute__ ((__mode__ (  __QI__ ))) ;
typedef int int16_t __attribute__ ((__mode__ (  __HI__ ))) ;
typedef int int32_t __attribute__ ((__mode__ (  __SI__ ))) ;
typedef int int64_t __attribute__ ((__mode__ (  __DI__ ))) ;


typedef unsigned int u_int8_t __attribute__ ((__mode__ (  __QI__ ))) ;
typedef unsigned int u_int16_t __attribute__ ((__mode__ (  __HI__ ))) ;
typedef unsigned int u_int32_t __attribute__ ((__mode__ (  __SI__ ))) ;
typedef unsigned int u_int64_t __attribute__ ((__mode__ (  __DI__ ))) ;

typedef int register_t __attribute__ ((__mode__ (__word__)));


 






 


 
# 1 "/usr/include/sys/select.h" 1 3
 


















 






 


 
# 1 "/usr/include/bits/select.h" 1 3
 

























# 36 "/usr/include/bits/select.h" 3












# 56 "/usr/include/bits/select.h" 3

# 72 "/usr/include/bits/select.h" 3

# 31 "/usr/include/sys/select.h" 2 3


 
# 1 "/usr/include/bits/sigset.h" 1 3
 





















typedef int __sig_atomic_t;

 


typedef struct
  {
    unsigned long int __val[(1024 / (8 * sizeof (unsigned long int))) ];
  } __sigset_t;




 





# 125 "/usr/include/bits/sigset.h" 3

# 34 "/usr/include/sys/select.h" 2 3


 

# 1 "/usr/include/time.h" 1 3
 

















 














# 51 "/usr/include/time.h" 3



# 62 "/usr/include/time.h" 3



# 73 "/usr/include/time.h" 3








 

struct timespec
  {
    long int tv_sec;		 
    long int tv_nsec;		 
  };





# 279 "/usr/include/time.h" 3



# 38 "/usr/include/sys/select.h" 2 3


 

 



struct timeval;

typedef __fd_mask fd_mask;

 
typedef __fd_set fd_set;

 



 




 






 




extern int __select  (int __nfds, __fd_set *__readfds,
			  __fd_set *__writefds, __fd_set *__exceptfds,
			  struct timeval *__timeout)    ;
extern int select  (int __nfds, __fd_set *__readfds,
			__fd_set *__writefds, __fd_set *__exceptfds,
			struct timeval *__timeout)    ;

# 91 "/usr/include/sys/select.h" 3


 


# 193 "/usr/include/sys/types.h" 2 3


 
# 1 "/usr/include/sys/sysmacros.h" 1 3
 





















 








# 47 "/usr/include/sys/sysmacros.h" 3



# 196 "/usr/include/sys/types.h" 2 3




 

typedef __blkcnt_t blkcnt_t;	  
typedef __fsblkcnt_t fsblkcnt_t;  
typedef __fsfilcnt_t fsfilcnt_t;  












 


# 65 "port.h" 2


# 1 "/usr/include/math.h" 1 3
 


















 








 

 

# 1 "/usr/include/bits/huge_val.h" 1 3
 

























 













 

# 68 "/usr/include/bits/huge_val.h" 3

# 33 "/usr/include/math.h" 2 3


 



 
# 1 "/usr/include/bits/mathdef.h" 1 3
 





















# 45 "/usr/include/bits/mathdef.h" 3

# 40 "/usr/include/math.h" 2 3



 



















# 1 "/usr/include/bits/mathcalls.h" 1 3
 


















 






























 

 
extern   double          acos          (double  __x)    ; extern   double         __acos          (double  __x)      ;
 
extern   double          asin          (double  __x)    ; extern   double         __asin          (double  __x)      ;
 
extern   double          atan          (double  __x)    ; extern   double         __atan          (double  __x)      ;
 
extern   double          atan2          (double  __y, double  __x)    ; extern   double         __atan2          (double  __y, double  __x)      ;

 
extern   double          cos          (double  __x)    ; extern   double         __cos          (double  __x)      ;
 
extern   double          sin          (double  __x)    ; extern   double         __sin          (double  __x)      ;
 
extern   double          tan          (double  __x)    ; extern   double         __tan          (double  __x)      ;







 

 
extern   double          cosh          (double  __x)    ; extern   double         __cosh          (double  __x)      ;
 
extern   double          sinh          (double  __x)    ; extern   double         __sinh          (double  __x)      ;
 
extern   double          tanh          (double  __x)    ; extern   double         __tanh          (double  __x)      ;


 
extern   double          acosh          (double  __x)    ; extern   double         __acosh          (double  __x)      ;
 
extern   double          asinh          (double  __x)    ; extern   double         __asinh          (double  __x)      ;
 
extern   double          atanh          (double  __x)    ; extern   double         __atanh          (double  __x)      ;


 

 
extern   double          exp          (double  __x)    ; extern   double         __exp          (double  __x)      ;








 
extern   double          frexp          (double  __x, int *__exponent)    ; extern   double         __frexp          (double  __x, int *__exponent)      ;

 
extern   double          ldexp          (double  __x, int __exponent)    ; extern   double         __ldexp          (double  __x, int __exponent)      ;

 
extern   double          log          (double  __x)    ; extern   double         __log          (double  __x)      ;

 
extern   double          log10          (double  __x)    ; extern   double         __log10          (double  __x)      ;

 
extern   double          modf          (double  __x, double  *__iptr)    ; extern   double         __modf          (double  __x, double  *__iptr)      ;


 
extern   double          expm1          (double  __x)    ; extern   double         __expm1          (double  __x)      ;

 
extern   double          log1p          (double  __x)    ; extern   double         __log1p          (double  __x)      ;

 
extern   double          logb          (double  __x)    ; extern   double         __logb          (double  __x)      ;











 

 
extern   double          pow          (double  __x, double  __y)    ; extern   double         __pow          (double  __x, double  __y)      ;

 
extern   double          sqrt          (double  __x)    ; extern   double         __sqrt          (double  __x)      ;


 
extern   double          hypot          (double  __x, double  __y)    ; extern   double         __hypot          (double  __x, double  __y)      ;



 
extern   double          cbrt          (double  __x)    ; extern   double         __cbrt          (double  __x)      ;



 

 
extern   double          ceil          (double  __x)    ; extern   double         __ceil          (double  __x)      ;

 
extern   double          fabs          (double  __x)     __attribute__ (    (__const__)  ); extern   double         __fabs          (double  __x)     __attribute__ (    (__const__)  )  ;

 
extern   double          floor          (double  __x)    ; extern   double         __floor          (double  __x)      ;

 
extern   double          fmod          (double  __x, double  __y)    ; extern   double         __fmod          (double  __x, double  __y)      ;


 

extern  int     __isinf      (double  __value)   __attribute__ ((__const__));


 

extern  int     isinf      (double  __value)   __attribute__ ((__const__));

 
extern   int        finite        (double  __value)    __attribute__ (  (__const__) ); extern   int        __finite        (double  __value)    __attribute__ (  (__const__) ) ;

 





extern   double          infnan          (int __error)     __attribute__ (    (__const__)  ); extern   double         __infnan          (int __error)     __attribute__ (    (__const__)  )  ;

 
extern   double          drem          (double  __x, double  __y)    ; extern   double         __drem          (double  __x, double  __y)      ;


 
extern   double          significand          (double  __x)    ; extern   double         __significand          (double  __x)      ;



 
extern   double          copysign          (double  __x, double  __y)     __attribute__ (    (__const__)  ); extern   double         __copysign          (double  __x, double  __y)     __attribute__ (    (__const__)  )  ;









 
extern   int        isnan        (double  __value)    __attribute__ (  (__const__) ); extern   int        __isnan        (double  __value)    __attribute__ (  (__const__) ) ;

 
extern   double          j0          (double )    ; extern   double         __j0          (double )      ;
extern   double          j1          (double )    ; extern   double         __j1          (double )      ;
extern   double          jn          (int, double )    ; extern   double         __jn          (int, double )      ;
extern   double          y0          (double )    ; extern   double         __y0          (double )      ;
extern   double          y1          (double )    ; extern   double         __y1          (double )      ;
extern   double          yn          (int, double )    ; extern   double         __yn          (int, double )      ;




 
extern   double          erf          (double )    ; extern   double         __erf          (double )      ;
extern   double          erfc          (double )    ; extern   double         __erfc          (double )      ;
extern   double          lgamma          (double )    ; extern   double         __lgamma          (double )      ;
extern   double          tgamma          (double )    ; extern   double         __tgamma          (double )      ;



 
extern   double          gamma          (double )    ; extern   double         __gamma          (double )      ;



 


extern   double          lgamma_r              (double , int *__signgamp)    ; extern   double         __lgamma_r              (double , int *__signgamp)      ;




 

extern   double          rint          (double  __x)    ; extern   double         __rint          (double  __x)      ;

 
extern   double          nextafter          (double  __x, double  __y)     __attribute__ (    (__const__)  ); extern   double         __nextafter          (double  __x, double  __y)     __attribute__ (    (__const__)  )  ;




 
extern   double          remainder          (double  __x, double  __y)    ; extern   double         __remainder          (double  __x, double  __y)      ;


 
extern   double          scalb          (double  __x, double  __n)    ; extern   double         __scalb          (double  __x, double  __n)      ;


 
extern   double          scalbn          (double  __x, int __n)    ; extern   double         __scalbn          (double  __x, int __n)      ;

 
extern   int        ilogb        (double  __x)   ; extern   int        __ilogb        (double  __x)    ;


# 330 "/usr/include/bits/mathcalls.h" 3

# 63 "/usr/include/math.h" 2 3







 











# 1 "/usr/include/bits/mathcalls.h" 1 3
 


















 






























 

 
extern   float          acosf         (float   __x)    ; extern   float         __acosf         (float   __x)      ;
 
extern   float          asinf         (float   __x)    ; extern   float         __asinf         (float   __x)      ;
 
extern   float          atanf         (float   __x)    ; extern   float         __atanf         (float   __x)      ;
 
extern   float          atan2f         (float   __y, float   __x)    ; extern   float         __atan2f         (float   __y, float   __x)      ;

 
extern   float          cosf         (float   __x)    ; extern   float         __cosf         (float   __x)      ;
 
extern   float          sinf         (float   __x)    ; extern   float         __sinf         (float   __x)      ;
 
extern   float          tanf         (float   __x)    ; extern   float         __tanf         (float   __x)      ;







 

 
extern   float          coshf         (float   __x)    ; extern   float         __coshf         (float   __x)      ;
 
extern   float          sinhf         (float   __x)    ; extern   float         __sinhf         (float   __x)      ;
 
extern   float          tanhf         (float   __x)    ; extern   float         __tanhf         (float   __x)      ;


 
extern   float          acoshf         (float   __x)    ; extern   float         __acoshf         (float   __x)      ;
 
extern   float          asinhf         (float   __x)    ; extern   float         __asinhf         (float   __x)      ;
 
extern   float          atanhf         (float   __x)    ; extern   float         __atanhf         (float   __x)      ;


 

 
extern   float          expf         (float   __x)    ; extern   float         __expf         (float   __x)      ;








 
extern   float          frexpf         (float   __x, int *__exponent)    ; extern   float         __frexpf         (float   __x, int *__exponent)      ;

 
extern   float          ldexpf         (float   __x, int __exponent)    ; extern   float         __ldexpf         (float   __x, int __exponent)      ;

 
extern   float          logf         (float   __x)    ; extern   float         __logf         (float   __x)      ;

 
extern   float          log10f         (float   __x)    ; extern   float         __log10f         (float   __x)      ;

 
extern   float          modff         (float   __x, float   *__iptr)    ; extern   float         __modff         (float   __x, float   *__iptr)      ;


 
extern   float          expm1f         (float   __x)    ; extern   float         __expm1f         (float   __x)      ;

 
extern   float          log1pf         (float   __x)    ; extern   float         __log1pf         (float   __x)      ;

 
extern   float          logbf         (float   __x)    ; extern   float         __logbf         (float   __x)      ;











 

 
extern   float          powf         (float   __x, float   __y)    ; extern   float         __powf         (float   __x, float   __y)      ;

 
extern   float          sqrtf         (float   __x)    ; extern   float         __sqrtf         (float   __x)      ;


 
extern   float          hypotf         (float   __x, float   __y)    ; extern   float         __hypotf         (float   __x, float   __y)      ;



 
extern   float          cbrtf         (float   __x)    ; extern   float         __cbrtf         (float   __x)      ;



 

 
extern   float          ceilf         (float   __x)    ; extern   float         __ceilf         (float   __x)      ;

 
extern   float          fabsf         (float   __x)     __attribute__ (    (__const__)  ); extern   float         __fabsf         (float   __x)     __attribute__ (    (__const__)  )  ;

 
extern   float          floorf         (float   __x)    ; extern   float         __floorf         (float   __x)      ;

 
extern   float          fmodf         (float   __x, float   __y)    ; extern   float         __fmodf         (float   __x, float   __y)      ;


 

extern  int    __isinff     (float   __value)   __attribute__ ((__const__));


 

extern  int    isinff     (float   __value)   __attribute__ ((__const__));

 
extern   int       finitef       (float   __value)    __attribute__ (  (__const__) ); extern   int       __finitef       (float   __value)    __attribute__ (  (__const__) ) ;

 





extern   float          infnanf         (int __error)     __attribute__ (    (__const__)  ); extern   float         __infnanf         (int __error)     __attribute__ (    (__const__)  )  ;

 
extern   float          dremf         (float   __x, float   __y)    ; extern   float         __dremf         (float   __x, float   __y)      ;


 
extern   float          significandf         (float   __x)    ; extern   float         __significandf         (float   __x)      ;



 
extern   float          copysignf         (float   __x, float   __y)     __attribute__ (    (__const__)  ); extern   float         __copysignf         (float   __x, float   __y)     __attribute__ (    (__const__)  )  ;









 
extern   int       isnanf       (float   __value)    __attribute__ (  (__const__) ); extern   int       __isnanf       (float   __value)    __attribute__ (  (__const__) ) ;

 
extern   float          j0f         (float  )    ; extern   float         __j0f         (float  )      ;
extern   float          j1f         (float  )    ; extern   float         __j1f         (float  )      ;
extern   float          jnf         (int, float  )    ; extern   float         __jnf         (int, float  )      ;
extern   float          y0f         (float  )    ; extern   float         __y0f         (float  )      ;
extern   float          y1f         (float  )    ; extern   float         __y1f         (float  )      ;
extern   float          ynf         (int, float  )    ; extern   float         __ynf         (int, float  )      ;




 
extern   float          erff         (float  )    ; extern   float         __erff         (float  )      ;
extern   float          erfcf         (float  )    ; extern   float         __erfcf         (float  )      ;
extern   float          lgammaf         (float  )    ; extern   float         __lgammaf         (float  )      ;
extern   float          tgammaf         (float  )    ; extern   float         __tgammaf         (float  )      ;



 
extern   float          gammaf         (float  )    ; extern   float         __gammaf         (float  )      ;



 


extern   float          lgammaf_r            (float  , int *__signgamp)    ; extern   float         __lgammaf_r            (float  , int *__signgamp)      ;




 

extern   float          rintf         (float   __x)    ; extern   float         __rintf         (float   __x)      ;

 
extern   float          nextafterf         (float   __x, float   __y)     __attribute__ (    (__const__)  ); extern   float         __nextafterf         (float   __x, float   __y)     __attribute__ (    (__const__)  )  ;




 
extern   float          remainderf         (float   __x, float   __y)    ; extern   float         __remainderf         (float   __x, float   __y)      ;


 
extern   float          scalbf         (float   __x, float   __n)    ; extern   float         __scalbf         (float   __x, float   __n)      ;


 
extern   float          scalbnf         (float   __x, int __n)    ; extern   float         __scalbnf         (float   __x, int __n)      ;

 
extern   int       ilogbf       (float   __x)   ; extern   int       __ilogbf       (float   __x)    ;


# 330 "/usr/include/bits/mathcalls.h" 3

# 82 "/usr/include/math.h" 2 3





 











# 1 "/usr/include/bits/mathcalls.h" 1 3
 


















 






























 

 
extern   long double          acosl         (long double   __x)    ; extern   long double         __acosl         (long double   __x)      ;
 
extern   long double          asinl         (long double   __x)    ; extern   long double         __asinl         (long double   __x)      ;
 
extern   long double          atanl         (long double   __x)    ; extern   long double         __atanl         (long double   __x)      ;
 
extern   long double          atan2l         (long double   __y, long double   __x)    ; extern   long double         __atan2l         (long double   __y, long double   __x)      ;

 
extern   long double          cosl         (long double   __x)    ; extern   long double         __cosl         (long double   __x)      ;
 
extern   long double          sinl         (long double   __x)    ; extern   long double         __sinl         (long double   __x)      ;
 
extern   long double          tanl         (long double   __x)    ; extern   long double         __tanl         (long double   __x)      ;







 

 
extern   long double          coshl         (long double   __x)    ; extern   long double         __coshl         (long double   __x)      ;
 
extern   long double          sinhl         (long double   __x)    ; extern   long double         __sinhl         (long double   __x)      ;
 
extern   long double          tanhl         (long double   __x)    ; extern   long double         __tanhl         (long double   __x)      ;


 
extern   long double          acoshl         (long double   __x)    ; extern   long double         __acoshl         (long double   __x)      ;
 
extern   long double          asinhl         (long double   __x)    ; extern   long double         __asinhl         (long double   __x)      ;
 
extern   long double          atanhl         (long double   __x)    ; extern   long double         __atanhl         (long double   __x)      ;


 

 
extern   long double          expl         (long double   __x)    ; extern   long double         __expl         (long double   __x)      ;








 
extern   long double          frexpl         (long double   __x, int *__exponent)    ; extern   long double         __frexpl         (long double   __x, int *__exponent)      ;

 
extern   long double          ldexpl         (long double   __x, int __exponent)    ; extern   long double         __ldexpl         (long double   __x, int __exponent)      ;

 
extern   long double          logl         (long double   __x)    ; extern   long double         __logl         (long double   __x)      ;

 
extern   long double          log10l         (long double   __x)    ; extern   long double         __log10l         (long double   __x)      ;

 
extern   long double          modfl         (long double   __x, long double   *__iptr)    ; extern   long double         __modfl         (long double   __x, long double   *__iptr)      ;


 
extern   long double          expm1l         (long double   __x)    ; extern   long double         __expm1l         (long double   __x)      ;

 
extern   long double          log1pl         (long double   __x)    ; extern   long double         __log1pl         (long double   __x)      ;

 
extern   long double          logbl         (long double   __x)    ; extern   long double         __logbl         (long double   __x)      ;











 

 
extern   long double          powl         (long double   __x, long double   __y)    ; extern   long double         __powl         (long double   __x, long double   __y)      ;

 
extern   long double          sqrtl         (long double   __x)    ; extern   long double         __sqrtl         (long double   __x)      ;


 
extern   long double          hypotl         (long double   __x, long double   __y)    ; extern   long double         __hypotl         (long double   __x, long double   __y)      ;



 
extern   long double          cbrtl         (long double   __x)    ; extern   long double         __cbrtl         (long double   __x)      ;



 

 
extern   long double          ceill         (long double   __x)    ; extern   long double         __ceill         (long double   __x)      ;

 
extern   long double          fabsl         (long double   __x)     __attribute__ (    (__const__)  ); extern   long double         __fabsl         (long double   __x)     __attribute__ (    (__const__)  )  ;

 
extern   long double          floorl         (long double   __x)    ; extern   long double         __floorl         (long double   __x)      ;

 
extern   long double          fmodl         (long double   __x, long double   __y)    ; extern   long double         __fmodl         (long double   __x, long double   __y)      ;


 

extern  int    __isinfl     (long double   __value)   __attribute__ ((__const__));


 

extern  int    isinfl     (long double   __value)   __attribute__ ((__const__));

 
extern   int       finitel       (long double   __value)    __attribute__ (  (__const__) ); extern   int       __finitel       (long double   __value)    __attribute__ (  (__const__) ) ;

 





extern   long double          infnanl         (int __error)     __attribute__ (    (__const__)  ); extern   long double         __infnanl         (int __error)     __attribute__ (    (__const__)  )  ;

 
extern   long double          dreml         (long double   __x, long double   __y)    ; extern   long double         __dreml         (long double   __x, long double   __y)      ;


 
extern   long double          significandl         (long double   __x)    ; extern   long double         __significandl         (long double   __x)      ;



 
extern   long double          copysignl         (long double   __x, long double   __y)     __attribute__ (    (__const__)  ); extern   long double         __copysignl         (long double   __x, long double   __y)     __attribute__ (    (__const__)  )  ;









 
extern   int       isnanl       (long double   __value)    __attribute__ (  (__const__) ); extern   int       __isnanl       (long double   __value)    __attribute__ (  (__const__) ) ;

 
extern   long double          j0l         (long double  )    ; extern   long double         __j0l         (long double  )      ;
extern   long double          j1l         (long double  )    ; extern   long double         __j1l         (long double  )      ;
extern   long double          jnl         (int, long double  )    ; extern   long double         __jnl         (int, long double  )      ;
extern   long double          y0l         (long double  )    ; extern   long double         __y0l         (long double  )      ;
extern   long double          y1l         (long double  )    ; extern   long double         __y1l         (long double  )      ;
extern   long double          ynl         (int, long double  )    ; extern   long double         __ynl         (int, long double  )      ;




 
extern   long double          erfl         (long double  )    ; extern   long double         __erfl         (long double  )      ;
extern   long double          erfcl         (long double  )    ; extern   long double         __erfcl         (long double  )      ;
extern   long double          lgammal         (long double  )    ; extern   long double         __lgammal         (long double  )      ;
extern   long double          tgammal         (long double  )    ; extern   long double         __tgammal         (long double  )      ;



 
extern   long double          gammal         (long double  )    ; extern   long double         __gammal         (long double  )      ;



 


extern   long double          lgammal_r            (long double  , int *__signgamp)    ; extern   long double         __lgammal_r            (long double  , int *__signgamp)      ;




 

extern   long double          rintl         (long double   __x)    ; extern   long double         __rintl         (long double   __x)      ;

 
extern   long double          nextafterl         (long double   __x, long double   __y)     __attribute__ (    (__const__)  ); extern   long double         __nextafterl         (long double   __x, long double   __y)     __attribute__ (    (__const__)  )  ;




 
extern   long double          remainderl         (long double   __x, long double   __y)    ; extern   long double         __remainderl         (long double   __x, long double   __y)      ;


 
extern   long double          scalbl         (long double   __x, long double   __n)    ; extern   long double         __scalbl         (long double   __x, long double   __n)      ;


 
extern   long double          scalbnl         (long double   __x, int __n)    ; extern   long double         __scalbnl         (long double   __x, int __n)      ;

 
extern   int       ilogbl       (long double   __x)   ; extern   int       __ilogbl       (long double   __x)    ;


# 330 "/usr/include/bits/mathcalls.h" 3

# 99 "/usr/include/math.h" 2 3













 
extern int signgam;



 
# 232 "/usr/include/math.h" 3



 
typedef enum
{
  _IEEE_ = -1,	 
  _SVID_,	 
  _XOPEN_,	 
  _POSIX_,
  _ISOC_	 
} _LIB_VERSION_TYPE;

 


extern _LIB_VERSION_TYPE _LIB_VERSION;




 







struct exception

  {
    int type;
    char *name;
    double arg1;
    double arg2;
    double retval;
  };




extern int matherr  (struct exception *__exc)    ;




 







 

# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/float.h" 1 3
 



 

    


    


    


    


    


    


    


    


    


    


    



    


    


    


    


    


    


    


    


    



    


    


    



union __convert_long_double {
  unsigned __convert_long_double_i[4];
  long double __convert_long_double_d;
};


    


    


    


    


    


    




# 289 "/usr/include/math.h" 2 3


# 299 "/usr/include/math.h" 3



 
















 


# 336 "/usr/include/math.h" 3



 






 





# 407 "/usr/include/math.h" 3


 



# 67 "port.h" 2

# 1 "/usr/include/signal.h" 1 3
 

















 











 

# 1 "/usr/include/bits/sigset.h" 1 3
 


















# 33 "/usr/include/bits/sigset.h" 3



 












 



 














# 97 "/usr/include/bits/sigset.h" 3



 


extern int __sigismember (__const __sigset_t *, int);
extern int __sigaddset (__sigset_t *, int);
extern int __sigdelset (__sigset_t *, int);

# 122 "/usr/include/bits/sigset.h" 3




# 33 "/usr/include/signal.h" 2 3


 





typedef __sig_atomic_t sig_atomic_t;







typedef __sigset_t sigset_t;






# 1 "/usr/include/bits/signum.h" 1 3
 




















 









 









































 





# 56 "/usr/include/signal.h" 2 3








 
typedef void (*__sighandler_t)  (int)  ;

 


extern __sighandler_t __sysv_signal  (int __sig,
					  __sighandler_t __handler)    ;




 



extern __sighandler_t signal  (int __sig, __sighandler_t __handler)    ;
# 90 "/usr/include/signal.h" 3








 



extern int kill  (__pid_t __pid, int __sig)    ;



 


extern int killpg  (__pid_t __pgrp, int __sig)    ;


 
extern int raise  (int __sig)    ;


 
extern __sighandler_t ssignal  (int __sig, __sighandler_t __handler)    ;
extern int gsignal  (int __sig)    ;



 
extern void psignal  (int __sig, __const char *__s)    ;



 




extern int __sigpause  (int __sig_or_mask, int __is_sig)    ;


 

extern int sigpause  (int __mask)    ;










 




 


 
extern int sigblock  (int __mask)    ;

 
extern int sigsetmask  (int __mask)    ;

 
extern int siggetmask  (void)    ;











 

typedef __sighandler_t sig_t;





 

# 1 "/usr/include/time.h" 1 3
 

















 














# 51 "/usr/include/time.h" 3



# 62 "/usr/include/time.h" 3



# 73 "/usr/include/time.h" 3




# 89 "/usr/include/time.h" 3




# 279 "/usr/include/time.h" 3



# 185 "/usr/include/signal.h" 2 3


 
# 1 "/usr/include/bits/siginfo.h" 1 3
 


























 
typedef union sigval
  {
    int sival_int;
    void *sival_ptr;
  } sigval_t;




typedef struct siginfo
  {
    int si_signo;		 
    int si_errno;		 

    int si_code;		 

    union
      {
	int _pad[((128  / sizeof (int)) - 3) ];

	  
	struct
	  {
	    __pid_t si_pid;	 
	    __uid_t si_uid;	 
	  } _kill;

	 
	struct
	  {
	    unsigned int _timer1;
	    unsigned int _timer2;
	  } _timer;

	 
	struct
	  {
	    __pid_t si_pid;	 
	    __uid_t si_uid;	 
	    sigval_t si_sigval;	 
	  } _rt;

	 
	struct
	  {
	    __pid_t si_pid;	 
	    __uid_t si_uid;	 
	    int si_status;	 
	    __clock_t si_utime;
	    __clock_t si_stime;
	  } _sigchld;

	 
	struct
	  {
	    void *si_addr;	 
	  } _sigfault;

	 
	struct
	  {
	    int si_band;	 
	    int si_fd;
	  } _sigpoll;
      } _sifields;
  } siginfo_t;


 













 

enum
{
  SI_SIGIO = -5,		 

  SI_ASYNCIO,			 

  SI_MESGQ,			 

  SI_TIMER,			 

  SI_QUEUE,			 

  SI_USER			 

};


 
enum
{
  ILL_ILLOPC = 1,		 

  ILL_ILLOPN,			 

  ILL_ILLADR,			 

  ILL_ILLTRP,			 

  ILL_PRVOPC,			 

  ILL_PRVREG,			 

  ILL_COPROC,			 

  ILL_BADSTK			 

};

 
enum
{
  FPE_INTDIV = 1,		 

  FPE_INTOVF,			 

  FPE_FLTDIV,			 

  FPE_FLTOVF,			 

  FPE_FLTUND,			 

  FPE_FLTRES,			 

  FPE_FLTINV,			 

  FPE_FLTSUB			 

};

 
enum
{
  SEGV_MAPERR = 1,		 

  SEGV_ACCERR			 

};

 
enum
{
  BUS_ADRALN = 1,		 

  BUS_ADRERR,			 

  BUS_OBJERR			 

};

 
enum
{
  TRAP_BRKPT = 1,		 

  TRAP_TRACE			 

};

 
enum
{
  CLD_EXITED = 1,		 

  CLD_KILLED,			 

  CLD_DUMPED,			 

  CLD_TRAPPED,			 

  CLD_STOPPED,			 

  CLD_CONTINUED			 

};

 
enum
{
  POLL_IN = 1,			 

  POLL_OUT,			 

  POLL_MSG,			 

  POLL_ERR,			 

  POLL_PRI,			 

  POLL_HUP			 

};








 



typedef struct sigevent
  {
    sigval_t sigev_value;
    int sigev_signo;
    int sigev_notify;

    union
      {
	int _pad[((64  / sizeof (int)) - 3) ];

	struct
	  {
	    void (*_function)  (sigval_t)  ;  
	    void *_attribute;			   
	  } _sigev_thread;
      } _sigev_un;
  } sigevent_t;

 



 
enum
{
  SIGEV_SIGNAL = 0,		 

  SIGEV_NONE,			 

  SIGEV_THREAD			 

};


# 188 "/usr/include/signal.h" 2 3



 
extern int sigemptyset  (sigset_t *__set)    ;

 
extern int sigfillset  (sigset_t *__set)    ;

 
extern int sigaddset  (sigset_t *__set, int __signo)    ;

 
extern int sigdelset  (sigset_t *__set, int __signo)    ;

 
extern int sigismember  (__const sigset_t *__set, int __signo)    ;

# 217 "/usr/include/signal.h" 3


 

# 1 "/usr/include/bits/sigaction.h" 1 3
 






















 
struct sigaction
  {
     

    union
      {
	 
	__sighandler_t sa_handler;
	 
	void (*sa_sigaction)  (int, siginfo_t *, void *)  ;
      }
    __sigaction_handler;






     
    __sigset_t sa_mask;

     
    int sa_flags;

     
    void (*sa_restorer)  (void)  ;
  };

 













 





 



# 221 "/usr/include/signal.h" 2 3


 
extern int sigprocmask  (int __how,
			     __const sigset_t *__set, sigset_t *__oset)    ;

 

extern int sigsuspend  (__const sigset_t *__set)    ;

 
extern int __sigaction  (int __sig, __const struct sigaction *__act,
			     struct sigaction *__oact)    ;
extern int sigaction  (int __sig, __const struct sigaction *__act,
			   struct sigaction *__oact)    ;

 
extern int sigpending  (sigset_t *__set)    ;


 
extern int sigwait  (__const sigset_t *__set, int *__sig)    ;


 
extern int sigwaitinfo  (__const sigset_t *__set, siginfo_t *__info)    ;

 

extern int sigtimedwait  (__const sigset_t *__set, siginfo_t *__info,
			      __const struct timespec *__timeout)    ;

 

extern int sigqueue  (__pid_t __pid, int __sig,
			  __const union sigval __val)    ;






 

extern __const char *__const _sys_siglist[64 ];
extern __const char *__const sys_siglist[64 ];

 
struct sigvec
  {
    __sighandler_t sv_handler;	 
    int sv_mask;		 

    int sv_flags;		 

  };

 





 




extern int sigvec  (int __sig, __const struct sigvec *__vec,
			struct sigvec *__ovec)    ;


 
# 1 "/usr/include/bits/sigcontext.h" 1 3
 






















 



# 1 "/usr/include/asm/sigcontext.h" 1 3



 







struct _fpreg {
	unsigned short significand[4];
	unsigned short exponent;
};

struct _fpstate {
	unsigned long 	cw,
			sw,
			tag,
			ipoff,
			cssel,
			dataoff,
			datasel;
	struct _fpreg	_st[8];
	unsigned long	status;
};

struct sigcontext {
	unsigned short gs, __gsh;
	unsigned short fs, __fsh;
	unsigned short es, __esh;
	unsigned short ds, __dsh;
	unsigned long edi;
	unsigned long esi;
	unsigned long ebp;
	unsigned long esp;
	unsigned long ebx;
	unsigned long edx;
	unsigned long ecx;
	unsigned long eax;
	unsigned long trapno;
	unsigned long err;
	unsigned long eip;
	unsigned short cs, __csh;
	unsigned long eflags;
	unsigned long esp_at_signal;
	unsigned short ss, __ssh;
	struct _fpstate * fpstate;
	unsigned long oldmask;
	unsigned long cr2;
};



# 28 "/usr/include/bits/sigcontext.h" 2 3


# 294 "/usr/include/signal.h" 2 3


 
extern int sigreturn  (struct sigcontext *__scp)    ;






 


extern int siginterrupt  (int __sig, int __interrupt)    ;

# 1 "/usr/include/bits/sigstack.h" 1 3
 























 
struct sigstack
  {
    void *  ss_sp;		 
    int ss_onstack;		 
  };


 
enum
{
  SS_ONSTACK = 1,

  SS_DISABLE

};

 


 



 
typedef struct sigaltstack
  {
    void *  ss_sp;
    int ss_flags;
    size_t ss_size;
  } stack_t;
# 309 "/usr/include/signal.h" 2 3


 


extern int sigstack  (__const struct sigstack *__ss,
			  struct sigstack *__oss)    ;

 

extern int sigaltstack  (__const struct sigaltstack *__ss,
			     struct sigaltstack *__oss)    ;



# 342 "/usr/include/signal.h" 3


 


 
extern int __libc_current_sigrtmin  (void)    ;
 
extern int __libc_current_sigrtmax  (void)    ;



 


# 68 "port.h" 2


# 80 "port.h"




















 



 










 





















 
# 147 "port.h"



 

# 1 "/usr/include/stdlib.h" 1 3
 

















 







 





# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 1 3






 


# 19 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3



 


 





 


# 61 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 





 


















 





 

 

# 131 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 


# 188 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3





 




 


# 269 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3




# 283 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 

# 317 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3




 





















# 33 "/usr/include/stdlib.h" 2 3


 




 
typedef struct
  {
    int quot;			 
    int rem;			 
  } div_t;

 

typedef struct
  {
    long int quot;		 
    long int rem;		 
  } ldiv_t;



# 65 "/usr/include/stdlib.h" 3



 



 





 

extern size_t __ctype_get_mb_cur_max  (void)    ;


 
extern double atof  (__const char *__nptr)    ;
 
extern int atoi  (__const char *__nptr)    ;
 
extern long int atol  (__const char *__nptr)    ;


 
__extension__ extern long long int atoll  (__const char *__nptr)    ;


 
extern double strtod  (__const char *   __nptr,
			   char **   __endptr)    ;










 
extern long int strtol  (__const char *   __nptr,
			     char **   __endptr, int __base)    ;
 
extern unsigned long int strtoul  (__const char *   __nptr,
				       char **   __endptr,
				       int __base)    ;


 
__extension__
extern long long int strtoq  (__const char *   __nptr,
				  char **   __endptr, int __base)    ;
 
__extension__
extern unsigned long long int strtouq  (__const char *   __nptr,
					    char **   __endptr,
					    int __base)    ;



 

 
__extension__
extern long long int strtoll  (__const char *   __nptr,
				   char **   __endptr, int __base)    ;
 
__extension__
extern unsigned long long int strtoull  (__const char *   __nptr,
					     char **   __endptr,
					     int __base)    ;



# 190 "/usr/include/stdlib.h" 3



 


extern double __strtod_internal  (__const char *   __nptr,
				      char **   __endptr,
				      int __group)    ;
extern float __strtof_internal  (__const char *   __nptr,
				     char **   __endptr, int __group)    ;
extern long double  __strtold_internal  (__const char *
						  __nptr,
						char **   __endptr,
						int __group)    ;

extern long int __strtol_internal  (__const char *   __nptr,
					char **   __endptr,
					int __base, int __group)    ;



extern unsigned long int __strtoul_internal  (__const char *
						    __nptr,
						  char **   __endptr,
						  int __base, int __group)    ;




__extension__
extern long long int __strtoll_internal  (__const char *   __nptr,
					      char **   __endptr,
					      int __base, int __group)    ;



__extension__
extern unsigned long long int __strtoull_internal  (__const char *
							  __nptr,
							char **
							  __endptr,
							int __base,
							int __group)    ;




# 326 "/usr/include/stdlib.h" 3




 


extern char *l64a  (long int __n)    ;

 
extern long int a64l  (__const char *__s)    ;




 



 
extern int32_t random  (void)    ;

 
extern void srandom  (unsigned int __seed)    ;

 



extern void *  initstate  (unsigned int __seed, void *  __statebuf,
			       size_t __statelen)    ;

 

extern void *  setstate  (void *  __statebuf)    ;



 



struct random_data
  {
    int32_t *fptr;		 
    int32_t *rptr;		 
    int32_t *state;		 
    int rand_type;		 
    int rand_deg;		 
    int rand_sep;		 
    int32_t *end_ptr;		 
  };

extern int random_r  (struct random_data *   __buf,
			  int32_t *   __result)    ;

extern int srandom_r  (unsigned int __seed, struct random_data *__buf)    ;

extern int initstate_r  (unsigned int __seed,
			     void *    __statebuf,
			     size_t __statelen,
			     struct random_data *   __buf)    ;

extern int setstate_r  (void *    __statebuf,
			    struct random_data *   __buf)    ;




 
extern int rand  (void)    ;
 
extern void srand  (unsigned int __seed)    ;


 
extern int rand_r  (unsigned int *__seed)    ;




 

 
extern double drand48  (void)    ;
extern double erand48  (unsigned short int __xsubi[3])    ;

 
extern long int lrand48  (void)    ;
extern long int nrand48  (unsigned short int __xsubi[3])    ;

 
extern long int mrand48  (void)    ;
extern long int jrand48  (unsigned short int __xsubi[3])    ;

 
extern void srand48  (long int __seedval)    ;
extern unsigned short int *seed48  (unsigned short int __seed16v[3])    ;
extern void lcong48  (unsigned short int __param[7])    ;

 
struct drand48_data
  {
    unsigned short int x[3];	 
    unsigned short int a[3];	 
    unsigned short int c;	 
    unsigned short int old_x[3];  
    int init;			 
  };


 
extern int drand48_r  (struct drand48_data *   __buffer,
			   double *   __result)    ;
extern int erand48_r  (unsigned short int __xsubi[3],
			   struct drand48_data *   __buffer,
			   double *   __result)    ;

 
extern int lrand48_r  (struct drand48_data *   __buffer,
			   long int *   __result)    ;
extern int nrand48_r  (unsigned short int __xsubi[3],
			   struct drand48_data *   __buffer,
			   long int *   __result)    ;

 
extern int mrand48_r  (struct drand48_data *   __buffer,
			   long int *   __result)    ;
extern int jrand48_r  (unsigned short int __xsubi[3],
			   struct drand48_data *   __buffer,
			   long int *   __result)    ;

 
extern int srand48_r  (long int __seedval, struct drand48_data *__buffer)    ;

extern int seed48_r  (unsigned short int __seed16v[3],
			  struct drand48_data *__buffer)    ;

extern int lcong48_r  (unsigned short int __param[7],
			   struct drand48_data *__buffer)    ;







 
extern void *  malloc  (size_t __size)    ;
 
extern void *  calloc  (size_t __nmemb, size_t __size)    ;



 

extern void *  realloc  (void *  __ptr, size_t __size)    ;
 
extern void free  (void *  __ptr)    ;


 
extern void cfree  (void *  __ptr)    ;



# 1 "/usr/include/alloca.h" 1 3
 























# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 1 3






 


# 19 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3



 


 





 


# 61 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 





 


















 





 

 

# 131 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 


# 188 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3





 




 

# 271 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


# 283 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 

# 317 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3




 





















# 25 "/usr/include/alloca.h" 2 3


 

 


 
extern void *  alloca  (size_t __size)    ;





 


# 492 "/usr/include/stdlib.h" 2 3




 
extern void *  valloc  (size_t __size)    ;



 
extern void abort  (void)     __attribute__ ((__noreturn__));


 
extern int atexit  (void (*__func) (void))    ;


 

extern int __on_exit  (void (*__func) (int __status, void *  __arg),
			   void *  __arg)    ;
extern int on_exit  (void (*__func) (int __status, void *  __arg),
			 void *  __arg)    ;


 


extern void exit  (int __status)     __attribute__ ((__noreturn__));








 
extern char *getenv  (__const char *__name)    ;

 

extern char *__secure_getenv  (__const char *__name)    ;


 
 

extern int putenv  (__const char *__string)    ;



 

extern int setenv  (__const char *__name, __const char *__value,
			int __replace)    ;

 
extern void unsetenv  (__const char *__name)    ;



 


extern int clearenv  (void)    ;




 



extern char *mktemp  (char *__template)    ;

 




extern int mkstemp  (char *__template)    ;



 
extern int system  (__const char *__command)    ;










 





extern char *realpath  (__const char *   __name,
			    char *   __resolved)    ;



 


typedef int (*__compar_fn_t)  (__const void * , __const void * )  ;






 

extern void *  bsearch  (__const void *  __key, __const void *  __base,
			       size_t __nmemb, size_t __size,
			       __compar_fn_t __compar)  ;

 

extern void qsort  (void *  __base, size_t __nmemb, size_t __size,
			  __compar_fn_t __compar)  ;


 
extern int abs  (int __x)     __attribute__ ((__const__));
extern long int labs  (long int __x)     __attribute__ ((__const__));






 

 
extern div_t div  (int __numer, int __denom)     __attribute__ ((__const__));
extern ldiv_t ldiv  (long int __numer, long int __denom)    
     __attribute__ ((__const__));








 


 


extern char *ecvt  (double __value, int __ndigit, int *   __decpt,
			int *   __sign)    ;

 


extern char *fcvt  (double __value, int __ndigit, int *   __decpt,
			int *   __sign)    ;

 


extern char *gcvt  (double __value, int __ndigit, char *__buf)    ;

 
extern char *qecvt  (long double  __value, int __ndigit,
			 int *   __decpt, int *   __sign)    ;
extern char *qfcvt  (long double  __value, int __ndigit,
			 int *   __decpt, int *   __sign)    ;
extern char *qgcvt  (long double  __value, int __ndigit, char *__buf)    ;



 

extern int ecvt_r  (double __value, int __ndigit, int *   __decpt,
			int *   __sign, char *   __buf,
			size_t __len)    ;
extern int fcvt_r  (double __value, int __ndigit, int *   __decpt,
			int *   __sign, char *   __buf,
			size_t __len)    ;

extern int qecvt_r  (long double  __value, int __ndigit,
			 int *   __decpt, int *   __sign,
			 char *   __buf, size_t __len)    ;
extern int qfcvt_r  (long double  __value, int __ndigit,
			 int *   __decpt, int *   __sign,
			 char *   __buf, size_t __len)    ;




 

extern int mblen  (__const char *__s, size_t __n)    ;
 

extern int mbtowc  (wchar_t *   __pwc,
			__const char *   __s, size_t __n)    ;
 

extern int wctomb  (char *__s, wchar_t __wchar)    ;


 
extern size_t mbstowcs  (wchar_t *    __pwcs,
			     __const char *   __s, size_t __n)    ;
 
extern size_t wcstombs  (char *   __s,
			     __const wchar_t *   __pwcs, size_t __n)    ;



 



extern int rpmatch  (__const char *__response)    ;



# 732 "/usr/include/stdlib.h" 3



# 756 "/usr/include/stdlib.h" 3


# 766 "/usr/include/stdlib.h" 3





 


# 152 "port.h" 2

# 175 "port.h"



 

# 1 "/usr/include/string.h" 1 3
 

















 








 

 


# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 1 3






 


# 19 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3



 


 





 


# 61 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 





 


















 





 

 

# 131 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 


# 188 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3





 




 

# 271 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


# 283 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3


 

 

# 317 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/stddef.h" 3




 





















# 33 "/usr/include/string.h" 2 3



 
extern void *  memcpy  (void *    __dest,
			    __const void *    __src, size_t __n)    ;
 

extern void *  memmove  (void *  __dest, __const void *  __src,
			     size_t __n)    ;

 



extern void *  memccpy  (void *  __dest, __const void *  __src,
			     int __c, size_t __n)    ;



 
extern void *  memset  (void *  __s, int __c, size_t __n)    ;

 
extern int memcmp  (__const void *  __s1, __const void *  __s2,
			size_t __n)    ;

 
extern void *  memchr  (__const void *  __s, int __c, size_t __n)    ;








 
extern char *strcpy  (char *   __dest,
			  __const char *   __src)    ;
 
extern char *strncpy  (char *   __dest,
			   __const char *   __src, size_t __n)    ;

 
extern char *strcat  (char *   __dest,
			  __const char *   __src)    ;
 
extern char *strncat  (char *   __dest,
			   __const char *   __src, size_t __n)    ;

 
extern int strcmp  (__const char *__s1, __const char *__s2)    ;
 
extern int strncmp  (__const char *__s1, __const char *__s2, size_t __n)    ;

 
extern int strcoll  (__const char *__s1, __const char *__s2)    ;
 
extern size_t strxfrm  (char *   __dest,
			    __const char *   __src, size_t __n)    ;

# 107 "/usr/include/string.h" 3



 
extern char *__strdup  (__const char *__s)    ;
extern char *strdup  (__const char *__s)    ;


 






# 143 "/usr/include/string.h" 3


 
extern char *strchr  (__const char *__s, int __c)    ;
 
extern char *strrchr  (__const char *__s, int __c)    ;







 

extern size_t strcspn  (__const char *__s, __const char *__reject)    ;
 

extern size_t strspn  (__const char *__s, __const char *__accept)    ;
 
extern char *strpbrk  (__const char *__s, __const char *__accept)    ;
 
extern char *strstr  (__const char *__haystack, __const char *__needle)    ;









 
extern char *strtok  (char *   __s,
			  __const char *   __delim)    ;

 

extern char *__strtok_r  (char *   __s,
			      __const char *   __delim,
			      char **   __save_ptr)    ;

extern char *strtok_r  (char *   __s,
			    __const char *   __delim,
			    char **   __save_ptr)    ;


# 203 "/usr/include/string.h" 3



 
extern size_t strlen  (__const char *__s)    ;








 
extern char *strerror  (int __errnum)    ;

 

extern char *__strerror_r  (int __errnum, char *__buf, size_t __buflen)    ;
extern char *strerror_r  (int __errnum, char *__buf, size_t __buflen)    ;


 

extern void __bzero  (void *  __s, size_t __n)    ;


 
extern void bcopy  (__const void *  __src, void *  __dest, size_t __n)    ;

 
extern void bzero  (void *  __s, size_t __n)    ;

 
extern int bcmp  (__const void *  __s1, __const void *  __s2, size_t __n)    ;

 
extern char *index  (__const char *__s, int __c)    ;

 
extern char *rindex  (__const char *__s, int __c)    ;

 

extern int __ffs  (int __i)     __attribute__ ((const));
extern int ffs  (int __i)     __attribute__ ((const));

 









 
extern int __strcasecmp  (__const char *__s1, __const char *__s2)    ;
extern int strcasecmp  (__const char *__s1, __const char *__s2)    ;

 
extern int strncasecmp  (__const char *__s1, __const char *__s2,
			     size_t __n)    ;


# 277 "/usr/include/string.h" 3



 

extern char *strsep  (char **   __stringp,
			  __const char *   __delim)    ;


# 319 "/usr/include/string.h" 3




# 347 "/usr/include/string.h" 3



 


# 180 "port.h" 2

# 192 "port.h"






 







extern void  srandom();
 


 






extern void  sleep();


 



# 1 "/usr/include/assert.h" 1 3
 

















 



# 32 "/usr/include/assert.h" 3





 




# 56 "/usr/include/assert.h" 3


 

 
extern void __assert_fail  (__const char *__assertion,
				__const char *__file,
				unsigned int __line,
				__const char *__function)    
     __attribute__ ((__noreturn__));

 
extern void __assert_perror_fail  (int __errnum,
				       __const char *__file,
				       unsigned int __line,
				       __const char *__function)    
     __attribute__ ((__noreturn__));

 













 





















# 224 "port.h" 2

# 238 "port.h"



 

# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/limits.h" 1 3
 


 





 
# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/syslimits.h" 1 3
 





# 1 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/limits.h" 1 3
 


 

# 114 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/limits.h" 3



# 1 "/usr/include/limits.h" 1 3
 

















 









 
# 1 "/usr/include/bits/posix1_lim.h" 1 3
 

















 









 

 


 


 


 


 


 


 


 



 


 


 


 


 



 


 


 


 


 


 


 


 


 


 


 


 



 


 


 


 


 



 
# 1 "/usr/include/bits/local_lim.h" 1 3
 


















 





 
# 1 "/usr/include/linux/limits.h" 1 3



















# 27 "/usr/include/bits/local_lim.h" 2 3


 





 

 


 

 


 

 


 



 

# 126 "/usr/include/bits/posix1_lim.h" 2 3








 







# 30 "/usr/include/limits.h" 2 3




# 1 "/usr/include/bits/posix2_lim.h" 1 3
 

















 







 


 


 


 


 




 




 



 


 



 




 




































# 34 "/usr/include/limits.h" 2 3








 





 

# 121 "/usr/include/limits.h" 3




  








# 117 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/limits.h" 2 3




# 7 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/syslimits.h" 2 3


# 11 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/limits.h" 2 3





 



 



 




 





 



 












 

 




 



 








 



 













 



# 107 "/usr/lib/gcc-lib/i386-slackware-linux/egcs-2.91.66/include/limits.h" 3




 









# 243 "port.h" 2












# 5 "espresso.h" 2

# 1 "utility.h" 1



 

























    

 


 






# 1 "ansi.h" 1



 
















 























# 42 "utility.h" 2


extern  long  util_cpu_time
	() ;
extern  char *util_path_search
	 (char *program)  ;
extern  char *util_file_search
	 (char *file, char *path, char *mode)  ;
extern  int   util_pipefork
	 (char **argv, FILE **toCommand, FILE **fromCommand, int *pid)  ;
extern  int   util_csystem
	 (char *command)  ;
extern  char *util_print_time
	 (long t)  ;
extern  char *util_strsav
	 (char *ptr)  ;
extern  char *util_tilde_expand
	 (char *filename)  ;
extern  char *util_tilde_compress
	 (char *filename)  ;
extern  void util_register_user
	 (char *user, char *directory)  ;

























# 6 "espresso.h" 2

# 1 "sparse.h" 1



 



typedef struct sm_element_struct sm_element;
typedef struct sm_row_struct sm_row;
typedef struct sm_col_struct sm_col;
typedef struct sm_matrix_struct sm_matrix;


 


struct sm_element_struct {
    int row_num;		 
    int col_num;		 
    sm_element *next_row;	 
    sm_element *prev_row;	 
    sm_element *next_col;	 
    sm_element *prev_col;	 
    char *user_word;		 
};


 


struct sm_row_struct {
    int row_num;		 
    int length;			 
    int flag;			 
    sm_element *first_col;	 
    sm_element *last_col;	 
    sm_row *next_row;		 
    sm_row *prev_row;		 
    char *user_word;		 
};


 


struct sm_col_struct {
    int col_num;		 
    int length;			 
    int flag;			 
    sm_element *first_row;	 
    sm_element *last_row;	 
    sm_col *next_col;		 
    sm_col *prev_col;		 
    char *user_word;		 
};


 


struct sm_matrix_struct {
    sm_row **rows;		 
    int rows_size;		 
    sm_col **cols;		 
    int cols_size;		 
    sm_row *first_row;		 
    sm_row *last_row;		 
    int nrows;			 
    sm_col *first_col;		 
    sm_col *last_col;		 
    int ncols;			 
    char *user_word;		 
};




























extern sm_matrix *sm_alloc(), *sm_alloc_size(), *sm_dup();
extern void sm_free(), sm_delrow(), sm_delcol(), sm_resize();
extern void sm_write(), sm_print(), sm_dump(), sm_cleanup();
extern void sm_copy_row(), sm_copy_col();
extern void sm_remove(), sm_remove_element();
extern sm_element *sm_insert(), *sm_find();
extern sm_row *sm_longest_row();
extern sm_col *sm_longest_col();
extern int sm_read(), sm_read_compressed();

extern sm_row *sm_row_alloc(), *sm_row_dup(), *sm_row_and();
extern void sm_row_free(), sm_row_remove(), sm_row_print();
extern sm_element *sm_row_insert(), *sm_row_find();
extern int sm_row_contains(), sm_row_intersects();
extern int sm_row_compare(), sm_row_hash();

extern sm_col *sm_col_alloc(), *sm_col_dup(), *sm_col_and();
extern void sm_col_free(), sm_col_remove(), sm_col_print();
extern sm_element *sm_col_insert(), *sm_col_find();
extern int sm_col_contains(), sm_col_intersects();
extern int sm_col_compare(), sm_col_hash();

extern int sm_row_dominance(), sm_col_dominance(), sm_block_partition();


# 7 "espresso.h" 2

# 1 "mincov.h" 1
 
extern sm_row *sm_minimum_cover();
# 8 "espresso.h" 2















 

 




















 










 
typedef unsigned int *pset;

 
typedef struct set_family {
    int wsize;                   
    int sf_size;                 
    int capacity;                
    int count;                   
    int active_count;            
    pset data;                   
    struct set_family *next;     
} set_family_t, *pset_family;

 



 






 





















 






 







 







 





 











 


 





 




 
# 178 "espresso.h"























































 
extern int bit_count[256];
 

 






 









 
typedef struct cost_struct {
    int cubes;			 
    int in;			 
    int out;			 
    int mv;			 
    int total;			 
    int primes;			 
} cost_t, *pcost;


 
typedef struct pair_struct {
    int cnt;
    int *var1;
    int *var2;
} pair_t, *ppair;


 
typedef struct symbolic_list_struct {
    int variable;
    int pos;
    struct symbolic_list_struct *next;
} symbolic_list_t;


 
typedef struct symbolic_label_struct {
    char *label;
    struct symbolic_label_struct *next;
} symbolic_label_t;


 
typedef struct symbolic_struct {
    symbolic_list_t *symbolic_list;	 
    int symbolic_list_length;		 
    symbolic_label_t *symbolic_label;	 
    int symbolic_label_length;		 
    struct symbolic_struct *next;
} symbolic_t;


 
typedef struct {
    pset_family  F, D, R;		 
    char *filename;              
    int pla_type;                
    pset  phase;                 
    ppair pair;                  
    char **label;		 
    symbolic_t *symbolic;	 
    symbolic_t *symbolic_output; 
} PLA_t, *pPLA;



 


 




 













 



















 



















 


































 



extern unsigned int debug;               
extern int  verbose_debug;               
extern char *total_name[16 ];     
extern long total_time[16 ];      
extern int total_calls[16 ];      

extern int  echo_comments;		 
extern int  echo_unknown_commands;	 
extern int  force_irredundant;           
extern int  skip_make_sparse;
extern int  kiss;                        
extern int  pos;                         
extern int  print_solution;              
extern int  recompute_onset;             
extern int  remove_essential;            
extern int  single_expand;               
extern int  summary;                     
extern int  trace;                       
extern int  unwrap_onset;                
extern int  use_random_order;		 
extern int  use_super_gasp;		 
extern char *filename;			 
extern int  debug_exact_minimization;    


 


struct pla_types_struct {
    char *key;
    int value;
};


 







struct cube_struct {
    int size;                    
    int num_vars;                
    int num_binary_vars;         
    int *first_part;             
    int *last_part;              
    int *part_size;              
    int *first_word;             
    int *last_word;              
    pset binary_mask;            
    pset mv_mask;                
    pset *var_mask;              
    pset *temp;                  
    pset fullset;                
    pset emptyset;               
    unsigned int inmask;         
    int inword;                  
    int *sparse;                 
    int num_mv_vars;             
    int output;                  
};

struct cdata_struct {
    int *part_zeros;             
    int *var_zeros;              
    int *parts_active;           
    int  *is_unate;              
    int vars_active;             
    int vars_unate;              
    int best;                    
};


extern struct pla_types_struct pla_types[];
/*extern*/ struct cube_struct cube, temp_cube_save;
extern struct cdata_struct cdata, temp_cdata_save;











 

 	extern int binate_split_select();
 	extern pset_family  cubeunlist();
 	extern pset  *cofactor();
 	extern pset  *cube1list();
 	extern pset  *cube2list();
 	extern pset  *cube3list();
 	extern pset  *scofactor();
 	extern void massive_count();
 	extern pset_family  complement();
 	extern pset_family  simplify();
 	extern void simp_comp();
 	extern int d1_rm_equal();
 	extern int rm2_contain();
 	extern int rm2_equal();
 	extern int rm_contain();
 	extern int rm_equal();
 	extern int rm_rev_contain();
 	extern pset *sf_list();
 	extern pset *sf_sort();
 	extern pset_family d1merge();
 	extern pset_family dist_merge();
 	extern pset_family sf_contain();
 	extern pset_family sf_dupl();
 	extern pset_family sf_ind_contain();
 	extern pset_family sf_ind_unlist();
 	extern pset_family sf_merge();
 	extern pset_family sf_rev_contain();
 	extern pset_family sf_union();
 	extern pset_family sf_unlist();
 	extern void cube_setup();
 	extern void restore_cube_struct();
 	extern void save_cube_struct();
 	extern void setdown_cube();
 	extern PLA_labels();
 	extern char *get_word();
 	extern int label_index();
 	extern int read_pla();
 	extern int read_symbolic();
 	extern pPLA new_PLA();
 	extern void PLA_summary();
 	extern void free_PLA();
 	extern void parse_pla();
 	extern void read_cube();
 	extern void skip_line();
 	extern foreach_output_function();
 	extern int cubelist_partition();
 	extern int so_both_do_espresso();
 	extern int so_both_do_exact();
 	extern int so_both_save();
 	extern int so_do_espresso();
 	extern int so_do_exact();
 	extern int so_save();
 	extern pset_family  cof_output();
 	extern pset_family  lex_sort();
 	extern pset_family  mini_sort();
 	extern pset_family  random_order();
 	extern pset_family  size_sort();
 	extern pset_family  sort_reduce();
 	extern pset_family  uncof_output();
 	extern pset_family  unravel();
 	extern pset_family  unravel_range();
 	extern void so_both_espresso();
 	extern void so_espresso();
 	extern char *fmt_cost();
 	extern char *print_cost();
 	extern char *strsav();
 	extern void copy_cost();
 	extern void cover_cost();
 	extern void fatal();
 	extern void print_trace();
 	extern void size_stamp();
 	extern void totals();
 	extern char *fmt_cube();
 	extern char *fmt_expanded_cube();
 	extern char *pc1();
 	extern char *pc2();
 	extern char *pc3();
 	extern int makeup_labels();
 	extern kiss_output();
 	extern kiss_print_cube();
 	extern output_symbolic_constraints();
 	extern void cprint();
 	extern void debug1_print();
 	extern void debug_print();
 	extern void eqn_output();
 	extern void fpr_header();
 	extern void fprint_pla();
 	extern void pls_group();
 	extern void pls_label();
 	extern void pls_output();
 	extern void print_cube();
 	extern void print_expanded_cube();
 	extern void sf_debug_print();
 	extern find_equiv_outputs();
 	extern int check_equiv();
 	extern pset_family  espresso();
 	extern int  essen_cube();
 	extern pset_family  cb_consensus();
 	extern pset_family  cb_consensus_dist0();
 	extern pset_family  essential();
 	extern pset_family  minimize_exact();
 	extern pset_family  minimize_exact_literals();
 	extern int  feasibly_covered();
 	extern int most_frequent();
 	extern pset_family  all_primes();
 	extern pset_family  expand();
 	extern pset_family  find_all_primes();
 	extern void elim_lowering();
 	extern void essen_parts();
 	extern void essen_raising();
 	extern void expand1();
 	extern void mincov();
 	extern void select_feasible();
 	extern void setup_BB_CC();
 	extern pset_family  expand_gasp();
 	extern pset_family  irred_gasp();
 	extern pset_family  last_gasp();
 	extern pset_family  super_gasp();
 	extern void expand1_gasp();
 	extern int getopt();
 	extern find_dc_inputs();
 	extern find_inputs();
 	extern form_bitvector();
 	extern map_dcset();
 	extern map_output_symbolic();
 	extern map_symbolic();
 	extern pset_family  map_symbolic_cover();
 	extern symbolic_hack_labels();
 	extern int  cube_is_covered();
 	extern int  taut_special_cases();
 	extern int  tautology();
 	extern pset_family  irredundant();
 	extern void mark_irredundant();
 	extern void irred_split_cover();
 	extern sm_matrix *irred_derive_table();
 	extern pset minterms();
 	extern void explode();
 	extern void map();
 	extern output_phase_setup();
 	extern pPLA set_phase();
 	extern pset_family  opo();
 	extern pset  find_phase();
 	extern pset_family find_covers();
 	extern pset_family form_cover_table();
 	extern pset_family opo_leaf();
 	extern pset_family opo_recur();
 	extern void opoall();
 	extern void phase_assignment();
 	extern void repeated_phase_assignment();
 	extern generate_all_pairs();
 	extern int **find_pairing_cost();
 	extern int find_best_cost();
 	extern int greedy_best_cost();
 	extern int minimize_pair();
 	extern int pair_free();
 	extern pair_all();
 	extern pset_family  delvar();
 	extern pset_family  pairvar();
 	extern ppair pair_best_cost();
 	extern ppair pair_new();
 	extern ppair pair_save();
 	extern print_pair();
 	extern void find_optimal_pairing();
 	extern void set_pair();
 	extern void set_pair1();
 	extern pset_family  primes_consensus();
 	extern int  sccc_special_cases();
 	extern pset_family  reduce();
 	extern pset  reduce_cube();
 	extern pset  sccc();
 	extern pset  sccc_cube();
 	extern pset  sccc_merge();
 	extern int  set_andp();
 	extern int  set_orp();
 	extern int  setp_disjoint();
 	extern int  setp_empty();
 	extern int  setp_equal();
 	extern int  setp_full();
 	extern int  setp_implies();
 	extern char *pbv1();
 	extern char *ps1();
 	extern int *sf_count();
 	extern int *sf_count_restricted();
 	extern int bit_index();
 	extern int set_dist();
 	extern int set_ord();
 	extern void set_adjcnt();
 	extern pset set_and();
 	extern pset set_clear();
 	extern pset set_copy();
 	extern pset set_diff();
 	extern pset set_fill();
 	extern pset set_merge();
 	extern pset set_or();
 	extern pset set_xor();
 	extern pset sf_and();
 	extern pset sf_or();
 	extern pset_family sf_active();
 	extern pset_family sf_addcol();
 	extern pset_family sf_addset();
 	extern pset_family sf_append();
 	extern pset_family sf_bm_read();
 	extern pset_family sf_compress();
 	extern pset_family sf_copy();
 	extern pset_family sf_copy_col();
 	extern pset_family sf_delc();
 	extern pset_family sf_delcol();
 	extern pset_family sf_inactive();
 	extern pset_family sf_join();
 	extern pset_family sf_new();
 	extern pset_family sf_permute();
 	extern pset_family sf_read();
 	extern pset_family sf_save();
 	extern pset_family sf_transpose();
 	extern void set_write();
 	extern void sf_bm_print();
 	extern void sf_cleanup();
 	extern void sf_delset();
 	extern void sf_free();
 	extern void sf_print();
 	extern void sf_write();
 	extern int  ccommon();
 	extern int  cdist0();
 	extern int  full_row();
 	extern int ascend();
 	extern int cactive();
 	extern int cdist();
 	extern int cdist01();
 	extern int cvolume();
 	extern int d1_order();
 	extern int d1_order_size();
 	extern int desc1();
 	extern int descend();
 	extern int lex_order();
 	extern int lex_order1();
 	extern pset force_lower();
 	extern void consensus();
 	extern pset_family  cb1_dsharp();
 	extern pset_family  cb_dsharp();
 	extern pset_family  cb_recur_dsharp();
 	extern pset_family  cb_recur_sharp();
 	extern pset_family  cb_sharp();
 	extern pset_family  cv_dsharp();
 	extern pset_family  cv_intersect();
 	extern pset_family  cv_sharp();
 	extern pset_family  dsharp();
 	extern pset_family  make_disjoint();
 	extern pset_family  sharp();
 pset do_sm_minimum_cover();
 	extern pset_family  make_sparse();
 	extern pset_family  mv_reduce();
 
 	extern qst();
 	extern pset_family  find_all_minimal_covers_petrick();
 	extern pset_family  map_cover_to_unate();
 	extern pset_family  map_unate_to_cover();
 	extern pset_family exact_minimum_cover();
 	extern pset_family gen_primes();
 	extern pset_family unate_compl();
 	extern pset_family unate_complement();
 	extern pset_family unate_intersect();
 	extern PLA_permute();
 	extern int  PLA_verify();
 	extern int  check_consistency();
 	extern int  verify();
# 1 "cof.c" 2


 



























 
pset  *cofactor(T, c)
  pset  *T;
  register pset  c;
{
    pset  temp = cube.temp[0], *Tc_save, *Tc, *T1;
    register pset  p;
    int listlen;

    
# 49 "cof.c"


     
    for(T1 = T+2; (p = *T1++) != ((void *)0) ; ) {
	if (p != c) {


            {
              register int w, last;
              register unsigned int x;

              if ((last=cube.inword) != -1) {
                x = p[last] & c[last];
                if (~(x|x>>1) & cube.inmask)
                  goto false;
                for (w=1;w<last;w++) {
                  x = p[w] & c[w];
                  if (~(x|x>>1) & 0x55555555 )
                    goto false;
                }
              }
            }

            {
              register int w, var, last;
              register pset  mask;

              for (var=cube.num_binary_vars; var<cube.num_vars; var++) {
                mask = cube.var_mask[var];
                last = cube.last_word[var];
                for (w=cube.first_word[var]; w<=last; w++)
                  if (p[w] & c[w] & mask[w])
                    goto nextvar;
                goto false;
                nextvar:;
              }
            }


	    *Tc++ = p;
	false: ;
	}
    }

    *Tc++ = (pset ) ((void *)0) ;                        
    Tc_save[1] = (pset ) Tc;                     
    return Tc_save;
}


# 400 "cof.c"

int main()
{
  return 0;
}
