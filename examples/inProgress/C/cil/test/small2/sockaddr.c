typedef unsigned short int sa_family_t;

typedef signed short int __int16_t;

typedef unsigned char		uint8_t;
typedef unsigned short int	uint16_t;
typedef unsigned int		uint32_t;

typedef unsigned int socklen_t;

struct sockaddr
  {
    sa_family_t  sa_family ;
    char sa_data[14];
  };


struct in_addr
  {
    uint32_t s_addr;
  };

struct sockaddr_in
  {
    sa_family_t  sin_family ;
    uint16_t sin_port;
    struct in_addr sin_addr;


    unsigned char sin_zero[sizeof (struct sockaddr) -
			   (sizeof (unsigned short int))  -
			   sizeof (uint16_t) -
			   sizeof (struct in_addr)];
  };

struct in6_addr
  {
    union
      {
	uint8_t		u6_addr8[16];
	uint16_t	u6_addr16[8];
	uint32_t	u6_addr32[4];
      } in6_u;
  };

struct sockaddr_in6
  {
    sa_family_t  sin6_family ;
    uint16_t sin6_port;
    uint32_t sin6_flowinfo;
    struct in6_addr sin6_addr;
  };


union sockunion {
	struct sockinet {
		sa_family_t  si_family ;
		uint16_t si_port;
	} su_si;
	struct sockaddr_in su_sin;
	struct sockaddr_in6 su_sin6;
};

union sockunion server_addr;

typedef union {
  __const struct  sockaddr  *__sockaddr__;
  //__const struct  sockaddr_at  *__sockaddr_at__;
  //__const struct  sockaddr_ax25  *__sockaddr_ax25__;
  //__const struct  sockaddr_dl  *__sockaddr_dl__;
  //__const struct  sockaddr_eon  *__sockaddr_eon__;
  __const struct  sockaddr_in  *__sockaddr_in__;
  __const struct  sockaddr_in6  *__sockaddr_in6__;
  //__const struct  sockaddr_inarp  *__sockaddr_inarp__;
  //__const struct  sockaddr_ipx  *__sockaddr_ipx__;
  //__const struct  sockaddr_iso  *__sockaddr_iso__;
  //__const struct  sockaddr_ns  *__sockaddr_ns__;
  //__const struct  sockaddr_un  *__sockaddr_un__;
  //__const struct  sockaddr_x25  *__sockaddr_x25__;
} __CONST_SOCKADDR_ARG __attribute__ ((__transparent_union__));

extern int bind  (int __fd, __CONST_SOCKADDR_ARG __addr, socklen_t __len)    ;

//extern int __libc_sa_len  (sa_family_t __af)    ;

int main()
{
  int ctl_sock=0;
  struct sockaddr *addrptr;
                           
  addrptr = (struct sockaddr *)&server_addr;
  bind(ctl_sock, addrptr, 3);
           //__libc_sa_len(( (struct sockaddr *)&server_addr )->sa_family) );

  return ctl_sock;
}

