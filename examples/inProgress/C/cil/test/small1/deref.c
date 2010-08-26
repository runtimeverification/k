//this case illustrates an "invalid type argument of '->' (tries to 
//dereference something that is not a pointer) when INFERBOX=infer

#define __FD_SETSIZE 1024

//the following two defines are from <bits/select.h>, which can normally 
//only be included from <sys/select.h>, but are included here to 
//"conglomerate" all the source files needed for this test case.

# define __FD_SET(fd, fdsp) \
  __asm__ __volatile__ ("btsl %1,%0"					      \
			: "=m" (__FDS_BITS (fdsp)[__FDELT (fd)])	      \
			: "r" (((int) (fd)) % __NFDBITS)		      \
			: "cc","memory")

# define __FD_CLR(fd, fdsp) \
  __asm__ __volatile__ ("btrl %1,%0"					      \
			: "=m" (__FDS_BITS (fdsp)[__FDELT (fd)])	      \
			: "r" (((int) (fd)) % __NFDBITS)		      \
			: "cc","memory")

typedef long int __fd_mask;

/* It's easier to assume 8-bit bytes than to get CHAR_BIT.  */
#define __NFDBITS	(8 * sizeof (__fd_mask))

/* fd_set for select and pselect.  */
typedef struct
  {
#ifdef __USE_XOPEN
    __fd_mask fds_bits[__FD_SETSIZE / __NFDBITS];
# define __FDS_BITS(set) ((set)->fds_bits)
#else
    __fd_mask __fds_bits[__FD_SETSIZE / __NFDBITS];
# define __FDS_BITS(set) ((set)->__fds_bits)
#endif
  } fd_set;

/* Maximum number of file descriptors in `fd_set'.  */
#define	FD_SETSIZE		__FD_SETSIZE

/* Access macros for `fd_set'.  */
#define	FD_SET(fd, fdsetp)	__FD_SET (fd, fdsetp)
#define	FD_CLR(fd, fdsetp)	__FD_CLR (fd, fdsetp)
#define	FD_ISSET(fd, fdsetp)	__FD_ISSET (fd, fdsetp)
#define	FD_ZERO(fdsetp)		__FD_ZERO (fdsetp)

typedef struct isc_mem {
  unsigned int magic;
} isc_mem_t;

/* The fd_set member is required to be an array of longs.  */
typedef long int __fd_mask;

typedef struct isc_socketmgr {
  isc_mem_t	       *mctx;
  fd_set			read_fds;
  fd_set			write_fds;
  int			fdstate[FD_SETSIZE];
} isc_socketmgr_t;

typedef struct isc_socket {
  isc_socketmgr_t	       *manager;
  int			fd;
} isc_socket_t;

typedef struct isc_socketevent {
	unsigned int		minimum;	
} isc_socketevent_t;

static void
wakeup_socket(isc_socketmgr_t *manager, int fd, int msg) {
	isc_socket_t *sock;

	if (manager->fdstate[fd] == 0) {
	  FD_CLR(fd, &manager->read_fds);
	  FD_CLR(fd, &manager->write_fds);
	  return;
	}
	FD_SET(sock->fd, &manager->read_fds);
	FD_SET(sock->fd, &manager->write_fds);
}

static void
allocate_socketevent(isc_socket_t *sock, unsigned int eventtype,
		     int action, const void *arg)
{
  isc_socketevent_t *ev;
  
  ev = (isc_socketevent_t *)isc_event_allocate(sock->manager->mctx,
					       sock, eventtype,
					       action, arg,
					       sizeof (*ev));
  
}










