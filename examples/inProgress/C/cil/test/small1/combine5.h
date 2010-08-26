typedef long int __time_t;

typedef __time_t time_t;

extern  struct 
{
			 
	time_t	to_initial;	 
	time_t	to_mail;	 
	time_t	to_rcpt;	 
	time_t	to_datainit;	 
	time_t	to_datablock;	 
	time_t	to_datafinal;	 
	time_t	to_nextcommand;	 
			 
	time_t	to_iconnect;	 
	time_t	to_connect;	 
	time_t	to_rset;	 
	time_t	to_helo;	 
	time_t	to_quit;	 
	time_t	to_miscshort;	 
	time_t	to_ident;	 
	time_t	to_fileopen;	 
	time_t	to_control;	 
			 
	time_t	to_q_return[8 ];	 
	time_t	to_q_warning[8 ];	 
	time_t	res_retrans[3 ];	 
	int	res_retry[3 ];	 
} TimeOuts;
