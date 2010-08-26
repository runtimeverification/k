// bind-used-not-defined.c:1316: label `cleanup' used but not defined
typedef unsigned short isc_uint16_t;
typedef unsigned int isc_uint32_t;
typedef enum __anonenum_isc_boolean_t_16 isc_boolean_t;
typedef enum __anonenum_isc_assertiontype_t_17 isc_assertiontype_t;
typedef struct isc_buffer isc_buffer_t;
typedef struct isc_event isc_event_t;
typedef unsigned int isc_eventtype_t;
typedef struct isc_interval isc_interval_t;
typedef struct isc_log isc_log_t;
typedef struct isc_logcategory isc_logcategory_t;
typedef struct isc_logmodule isc_logmodule_t;
typedef struct isc_mem isc_mem_t;
typedef struct isc_netaddr isc_netaddr_t;
typedef struct isc_quota isc_quota_t;
typedef struct isc_region isc_region_t;
typedef unsigned int isc_result_t;
typedef struct isc_sockaddr isc_sockaddr_t;
typedef struct isc_socket isc_socket_t;
typedef struct isc_socketevent isc_socketevent_t;
typedef struct isc_task isc_task_t;
typedef struct isc_time isc_time_t;
typedef struct isc_timer isc_timer_t;
typedef int isc_mutex_t;
struct __anonstruct_isc__magic_t_22
{
  unsigned int magic;
};
typedef struct __anonstruct_isc__magic_t_22 isc__magic_t;
typedef unsigned short sa_family_t;
struct sockaddr
{
  sa_family_t sa_family;
};
struct in6_pktinfo
{
  struct in6_addr ipi6_addr;
};
struct isc_region
{
  unsigned char *base;
  unsigned int length;
};
typedef struct dns_acl dns_acl_t;
typedef struct dns_aclelement dns_aclelement_t;
typedef struct dns_aclenv dns_aclenv_t;
typedef struct dns_dispatch dns_dispatch_t;
typedef struct dns_message dns_message_t;
typedef isc_uint16_t dns_messageid_t;
typedef struct dns_name dns_name_t;
typedef isc_uint16_t dns_rcode_t;
typedef isc_uint16_t dns_rdataclass_t;
typedef struct dns_rdataset dns_rdataset_t;
typedef struct dns_resolver dns_resolver_t;
typedef struct dns_tsig_keyring dns_tsig_keyring_t;
typedef isc_uint32_t dns_ttl_t;
typedef struct dns_view dns_view_t;
struct __anonstruct_dns_viewlist_t_34
{
  dns_view_t *head;
};
typedef struct __anonstruct_dns_viewlist_t_34 dns_viewlist_t;
struct isc_event
{
  isc_eventtype_t ev_type;
  void *ev_arg;
  void *ev_sender;
};
typedef isc_uint32_t isc_stdtime_t;
union __anonunion_type_55
{
  struct sockaddr sa;
};
struct isc_sockaddr
{
  union __anonunion_type_55 type;
};
struct isc_socketevent
{
  isc_eventtype_t ev_type;
  void *ev_arg;
  isc_result_t result;
  unsigned int n;
  isc_region_t region;
  isc_sockaddr_t address;
  struct in6_pktinfo pktinfo;
  isc_uint32_t attributes;
};
struct dns_message
{
  dns_messageid_t id;
  dns_rcode_t rcode;
  unsigned int opcode;
  dns_rdataclass_t rdclass;
  dns_rcode_t tsigstatus;
};
struct dns_rdataset
{
  dns_rdataclass_t rdclass;
  dns_ttl_t ttl;
};
struct __anonstruct_link_78
{
  struct dns_view *next;
};
struct dns_view
{
  dns_rdataclass_t rdclass;
  char *name;
  dns_resolver_t *resolver;
  isc_boolean_t recursion;
  dns_acl_t *recursionacl;
  dns_acl_t *matchclients;
  dns_acl_t *matchdestinations;
  isc_boolean_t matchrecursiveonly;
  struct __anonstruct_link_78 link;
};
typedef struct ns_client ns_client_t;
typedef struct ns_clientmgr ns_clientmgr_t;
typedef struct ns_server ns_server_t;
typedef struct ns_interface ns_interface_t;
struct ns_interface
{
  isc_sockaddr_t addr;
};
struct dns_tcpmsg
{
  isc_buffer_t buffer;
  isc_result_t result;
};
typedef struct dns_tcpmsg dns_tcpmsg_t;
struct __anonstruct_client_list_t_87
{
  ns_client_t *head;
  ns_client_t *tail;
};
typedef struct __anonstruct_client_list_t_87 client_list_t;
struct __anonstruct_link_89
{
  ns_client_t *prev;
  ns_client_t *next;
};
struct ns_client
{
  unsigned int magic;
  isc_mem_t *mctx;
  ns_clientmgr_t *manager;
  int state;
  int newstate;
  int naccepts;
  int nreads;
  int nsends;
  int nrecvs;
  int nctls;
  int references;
  unsigned int attributes;
  isc_task_t *task;
  dns_view_t *view;
  dns_dispatch_t *dispatch;
  isc_socket_t *udpsocket;
  isc_socket_t *tcplistener;
  isc_socket_t *tcpsocket;
  unsigned char *tcpbuf;
  dns_tcpmsg_t tcpmsg;
  isc_boolean_t tcpmsg_valid;
  isc_timer_t *timer;
  isc_boolean_t timerset;
  dns_message_t *message;
  isc_socketevent_t *sendevent;
  isc_socketevent_t *recvevent;
  unsigned char *recvbuf;
  dns_rdataset_t *opt;
  isc_uint16_t udpsize;
  isc_uint16_t extflags;
  isc_stdtime_t requesttime;
  isc_stdtime_t now;
  dns_name_t signername;
  dns_name_t *signer;
  isc_boolean_t mortal;
  isc_quota_t *tcpquota;
  isc_quota_t *recursionquota;
  ns_interface_t *interface;
  isc_sockaddr_t peeraddr;
  isc_boolean_t peeraddr_valid;
  struct in6_pktinfo pktinfo;
  struct __anonstruct_link_89 link;
  client_list_t *list;
};
struct ns_server
{
  dns_acl_t *blackholeacl;
  dns_aclenv_t aclenv;
  dns_viewlist_t viewlist;
};
struct ns_clientmgr
{
  isc_mutex_t lock;
  isc_boolean_t exiting;
  client_list_t active;
  client_list_t inactive;
};
void (*isc_assertion_failed) (char const *, int, isc_assertiontype_t,
			      char const *);
isc_logcategory_t dns_categories[11];
ns_server_t *ns_g_server;
isc_log_t *ns_g_lctx;
isc_logcategory_t *ns_g_categories;
isc_logmodule_t *ns_g_modules;
static isc_boolean_t
exit_check (ns_client_t * client)
{
  ns_clientmgr_t *locked_manager;
  ns_clientmgr_t *destroy_manager;
  int tmp;
  int tmp___0;
  int tmp___1;
  isc_socket_t *socket___0;
  int tmp___2;
  int tmp___3;
  int tmp___4;
  int tmp___6;
  int tmp___7;
  int tmp___8;
  int tmp___9;
  int tmp___11;
  isc_mutex_t tmp___12;
  int tmp___13;
  int tmp___14;
  int tmp___15;
  int tmp___16;
  int tmp___17;
  isc_boolean_t tmp___18;
  int tmp___19;
  ns_clientmgr_t *manager;
  int tmp___21;
  isc_mutex_t tmp___22;
  int tmp___23;
  int tmp___24;
  int tmp___25;
  int tmp___26;
  int tmp___27;
  {
    locked_manager = (ns_clientmgr_t *) ((void *) 0);
    destroy_manager = (ns_clientmgr_t *) ((void *) 0);
    if ((unsigned long) client != (unsigned long) ((void *) 0))
      {
	if (((isc__magic_t const *) client)->magic == 1314079587U)
	  {
	    tmp = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 205, 0,
				       (char const *)
				       "(((client) != ((void *)0)) && (((const isc__magic_t *)(client))->magic == ( ((\'N\') << 24 | (\'S\') << 16 | (\'C\') << 8 | (\'c\')))))");
	    tmp = 0;
	  }
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 205, 0,
				   (char const *)
				   "(((client) != ((void *)0)) && (((const isc__magic_t *)(client))->magic == ( ((\'N\') << 24 | (\'S\') << 16 | (\'C\') << 8 | (\'c\')))))");
	tmp = 0;
      }
    if (client->state <= client->newstate)
      {
	return (0);
      }
    if (client->newstate < 4)
      {
	tmp___0 = 1;
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 210, 2,
				   (char const *) "client->newstate < 4");
	tmp___0 = 0;
      }
    if (client->newstate == 0)
      {
	if ((unsigned long) client->view != (unsigned long) ((void *) 0))
	  {
	    dns_view_detach (&client->view);
	  }
      }
    if (client->state == 4)
      {
	if (client->newstate <= 3)
	  {
	    tmp___1 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 226, 2,
				       (char const *)
				       "client->newstate <= 3");
	    tmp___1 = 0;
	  }
	if (client->nsends > 0)
	  {
	    if ((client->attributes & 1U) != 0U)
	      {
		socket___0 = client->tcpsocket;
	      }
	    else
	      {
		socket___0 = client->udpsocket;
	      }
	    isc_socket_cancel (socket___0, client->task, 2U);
	  }
	if (client->nsends == 0)
	  {
	    if (client->nrecvs == 0)
	      {
		if (!(client->references == 0))
		  {
		    return (1);
		  }
	      }
	    else
	      {
		return (1);
	      }
	  }
	else
	  {
	    return (1);
	  }
	ns_client_endrequest (client);
	client->state = 3;
	if ((unsigned long) client->recursionquota ==
	    (unsigned long) ((void *) 0))
	  {
	    tmp___2 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 256, 2,
				       (char const *)
				       "client->recursionquota == ((void *)0)");
	    tmp___2 = 0;
	  }
	if (3 == client->newstate)
	  {
	    client_read (client);
	    client->newstate = 9;
	    return (1);
	  }
      }
    if (client->state == 3)
      {
	if ((unsigned long) client->recursionquota ==
	    (unsigned long) ((void *) 0))
	  {
	    tmp___3 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 269, 2,
				       (char const *)
				       "client->recursionquota == ((void *)0)");
	    tmp___3 = 0;
	  }
	if (client->newstate <= 2)
	  {
	    tmp___4 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 270, 2,
				       (char const *)
				       "client->newstate <= 2");
	    tmp___4 = 0;
	  }
	if (client->nreads > 0)
	  {
	    dns_tcpmsg_cancelread (&client->tcpmsg);
	  }
	if (!client->nreads == 0)
	  {
	    return (1);
	  }
	if (client->tcpmsg_valid)
	  {
	    dns_tcpmsg_invalidate (&client->tcpmsg);
	    client->tcpmsg_valid = 0;
	  }
	if ((unsigned long) client->tcpsocket != (unsigned long) ((void *) 0))
	  {
	    ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
			   (char const *) "%s", "closetcp");
	    isc_socket_detach (&client->tcpsocket);
	  }
	if ((unsigned long) client->tcpquota != (unsigned long) ((void *) 0))
	  {
	    isc_quota_detach (&client->tcpquota);
	  }
	if (client->timerset)
	  {
	    isc_timer_reset (client->timer, 2, (isc_time_t *) ((void *) 0),
			     (isc_interval_t *) ((void *) 0), 1);
	    client->timerset = 0;
	  }
	client->peeraddr_valid = 0;
	client->state = 2;
	if ((unsigned long) client->recursionquota ==
	    (unsigned long) ((void *) 0))
	  {
	    tmp___6 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 300, 2,
				       (char const *)
				       "client->recursionquota == ((void *)0)");
	    tmp___6 = 0;
	  }
	ns_client_checkactive (client);
	if (2 == client->newstate)
	  {
	    if ((client->attributes & 1U) != 0U)
	      {
		client_accept (client);
	      }
	    else
	      {
		client_udprecv (client);
	      }
	    client->newstate = 9;
	    return (1);
	  }
      }
    if (client->state == 2)
      {
	if (client->newstate <= 1)
	  {
	    tmp___7 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 321, 2,
				       (char const *)
				       "client->newstate <= 1");
	    tmp___7 = 0;
	  }
	if (client->naccepts > 0)
	  {
	    isc_socket_cancel (client->tcplistener, client->task, 4U);
	  }
	if (!(client->naccepts == 0))
	  {
	    return (1);
	  }
	if (client->nrecvs > 0)
	  {
	    isc_socket_cancel (client->udpsocket, client->task, 1U);
	  }
	if (!(client->nrecvs == 0))
	  {
	    return (1);
	  }
	if (client->nctls > 0)
	  {
	    return (1);
	  }
	if (client->interface)
	  {
	    ns_interface_detach (&client->interface);
	  }
	if (client->naccepts == 0)
	  {
	    tmp___8 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 353, 2,
				       (char const *)
				       "client->naccepts == 0");
	    tmp___8 = 0;
	  }
	if ((unsigned long) client->recursionquota ==
	    (unsigned long) ((void *) 0))
	  {
	    tmp___9 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 354, 2,
				       (char const *)
				       "client->recursionquota == ((void *)0)");
	    tmp___9 = 0;
	  }
	if ((unsigned long) client->tcplistener !=
	    (unsigned long) ((void *) 0))
	  {
	    isc_socket_detach (&client->tcplistener);
	  }
	if ((unsigned long) client->udpsocket != (unsigned long) ((void *) 0))
	  {
	    isc_socket_detach (&client->udpsocket);
	  }
	if ((unsigned long) client->dispatch != (unsigned long) ((void *) 0))
	  {
	    dns_dispatch_detach (&client->dispatch);
	  }
	client->attributes = 0U;
	client->mortal = 0;
	while (1)
	  {
	    tmp___12 = (client->manager)->lock;
	    (client->manager)->lock++;
	    if (tmp___12 == 0)
	      {
		tmp___11 = 0;
	      }
	    else
	      {
		tmp___11 = 34;
	      }
	    if (tmp___11 == 0)
	      {
		tmp___13 = 1;
	      }
	    else
	      {
		isc_error_runtimecheck ((char const *) "client.c", 367,
					(char const *)
					"((*((&client->manager->lock)))++ == 0 ? 0 : 34) == 0");
		tmp___13 = 0;
	      }
	    break;
	  }
	locked_manager = client->manager;
	while (1)
	  {
	    while (1)
	      {
		if ((unsigned long) client->link.next !=
		    (unsigned long) ((void *) 0))
		  {
		    (client->link.next)->link.prev = client->link.prev;
		  }
		else
		  {
		    (client->list)->tail = client->link.prev;
		  }
		if ((unsigned long) client->link.prev !=
		    (unsigned long) ((void *) 0))
		  {
		    (client->link.prev)->link.next = client->link.next;
		  }
		else
		  {
		    (client->list)->head = client->link.next;
		  }
		client->link.prev = (ns_client_t *) ((void *) -1);
		client->link.next = (ns_client_t *) ((void *) -1);
		break;
	      }
	    break;
	  }
	while (1)
	  {
	    while (1)
	      {
		if ((unsigned long) (client->manager)->inactive.tail !=
		    (unsigned long) ((void *) 0))
		  {
		    ((client->manager)->inactive.tail)->link.next = client;
		  }
		else
		  {
		    (client->manager)->inactive.head = client;
		  }
		client->link.prev = (client->manager)->inactive.tail;
		client->link.next = (ns_client_t *) ((void *) 0);
		(client->manager)->inactive.tail = client;
		break;
	      }
	    break;
	  }
	client->list = &(client->manager)->inactive;
	client->state = 1;
	if ((unsigned long) client->recursionquota ==
	    (unsigned long) ((void *) 0))
	  {
	    tmp___14 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 380, 2,
				       (char const *)
				       "client->recursionquota == ((void *)0)");
	    tmp___14 = 0;
	  }
	if (client->state == client->newstate)
	  {
	    client->newstate = 9;
	    goto unlock;
	  }
      }
    if (client->state == 1)
      {
	if (client->newstate == 0)
	  {
	    tmp___15 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 389, 2,
				       (char const *)
				       "client->newstate == 0");
	    tmp___15 = 0;
	  }
	if (client->state == 1)
	  {
	    tmp___16 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 398, 0,
				       (char const *) "client->state == 1");
	    tmp___16 = 0;
	  }
	if ((unsigned long) client->recursionquota ==
	    (unsigned long) ((void *) 0))
	  {
	    tmp___17 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 400, 2,
				       (char const *)
				       "client->recursionquota == ((void *)0)");
	    tmp___17 = 0;
	  }
	ns_query_free (client);
	while (1)
	  {
	    isc__mem_put (client->mctx, (void *) client->recvbuf, 4096U);
	    client->recvbuf = (unsigned char *) ((void *) 0);
	    break;
	  }
	isc_event_free ((isc_event_t **) (&client->sendevent));
	isc_event_free ((isc_event_t **) (&client->recvevent));
	isc_timer_detach (&client->timer);
	if ((unsigned long) client->tcpbuf != (unsigned long) ((void *) 0))
	  {
	    while (1)
	      {
		isc__mem_put (client->mctx, (void *) client->tcpbuf, 65537U);
		client->tcpbuf = (unsigned char *) ((void *) 0);
		break;
	      }
	  }
	if ((unsigned long) client->opt != (unsigned long) ((void *) 0))
	  {
	    tmp___18 = dns_rdataset_isassociated (client->opt);
	    if (tmp___18)
	      {
		tmp___19 = 1;
	      }
	    else
	      {
		((*isc_assertion_failed)) ((char const *) "client.c", 411, 2,
					   (char const *)
					   "dns_rdataset_isassociated(client->opt)");
		tmp___19 = 0;
	      }
	    dns_rdataset_disassociate (client->opt);
	    dns_message_puttemprdataset (client->message, &client->opt);
	  }
	dns_message_destroy (&client->message);
	if ((unsigned long) client->manager != (unsigned long) ((void *) 0))
	  {
	    manager = client->manager;
	    if ((unsigned long) locked_manager ==
		(unsigned long) ((void *) 0))
	      {
		while (1)
		  {
		    tmp___22 = manager->lock;
		    manager->lock++;
		    if (tmp___22 == 0)
		      {
			tmp___21 = 0;
		      }
		    else
		      {
			tmp___21 = 34;
		      }
		    if (tmp___21 == 0)
		      {
			tmp___23 = 1;
		      }
		    else
		      {
			isc_error_runtimecheck ((char const *) "client.c",
						419,
						(char const *)
						"((*((&manager->lock)))++ == 0 ? 0 : 34) == 0");
			tmp___23 = 0;
		      }
		    break;
		  }
		locked_manager = manager;
	      }
	    while (1)
	      {
		while (1)
		  {
		    if ((unsigned long) client->link.next !=
			(unsigned long) ((void *) 0))
		      {
			(client->link.next)->link.prev = client->link.prev;
		      }
		    else
		      {
			(client->list)->tail = client->link.prev;
		      }
		    if ((unsigned long) client->link.prev !=
			(unsigned long) ((void *) 0))
		      {
			(client->link.prev)->link.next = client->link.next;
		      }
		    else
		      {
			(client->list)->head = client->link.next;
		      }
		    client->link.prev = (ns_client_t *) ((void *) -1);
		    client->link.next = (ns_client_t *) ((void *) -1);
		    break;
		  }
		break;
	      }
	    client->list = (client_list_t *) ((void *) 0);
	    if (manager->exiting)
	      {
		if ((unsigned long) manager->active.head ==
		    (unsigned long) ((void *) 0))
		  {
		    tmp___24 = 1;
		  }
		else
		  {
		    tmp___24 = 0;
		  }
		if (tmp___24)
		  {
		    if ((unsigned long) manager->inactive.head ==
			(unsigned long) ((void *) 0))
		      {
			tmp___25 = 1;
		      }
		    else
		      {
			tmp___25 = 0;
		      }
		    if (tmp___25)
		      {
			destroy_manager = manager;
		      }
		  }
	      }
	  }
	if ((unsigned long) client->task != (unsigned long) ((void *) 0))
	  {
	    isc_task_detach (&client->task);
	  }
	ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
		       (char const *) "%s", "free");
	client->magic = 0U;
	while (1)
	  {
	    isc__mem_put (client->mctx, (void *) client, sizeof ((*client)));
	    client = (ns_client_t *) ((void *) 0);
	    break;
	  }
	goto unlock;
      }
  unlock:if ((unsigned long) locked_manager !=
	(unsigned long) ((void *) 0))
      {
	while (1)
	  {
	    locked_manager->lock--;
	    if (locked_manager->lock == 0)
	      {
		tmp___26 = 0;
	      }
	    else
	      {
		tmp___26 = 34;
	      }
	    if (tmp___26 == 0)
	      {
		tmp___27 = 1;
	      }
	    else
	      {
		isc_error_runtimecheck ((char const *) "client.c", 446,
					(char const *)
					"(--(*((&locked_manager->lock))) == 0 ? 0 : 34) == 0");
		tmp___27 = 0;
	      }
	    break;
	  }
	locked_manager = (ns_clientmgr_t *) ((void *) 0);
      }
    if ((unsigned long) destroy_manager != (unsigned long) ((void *) 0))
      {
	clientmgr_destroy (destroy_manager);
      }
    return (1);
  }
}
static void
client_senddone (isc_task_t * task, isc_event_t * event)
{
  ns_client_t *client;
  isc_socketevent_t *sevent;
  int tmp;
  int tmp___0;
  int tmp___1;
  int tmp___2;
  int tmp___3;
  char const *tmp___4;
  int tmp___5;
  int tmp___6;
  isc_boolean_t tmp___7;
  {
    sevent = (isc_socketevent_t *) event;
    if ((unsigned long) sevent != (unsigned long) ((void *) 0))
      {
	tmp = 1;
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 626, 0,
				   (char const *) "sevent != ((void *)0)");
	tmp = 0;
      }
    if (sevent->ev_type == 131074U)
      {
	tmp___0 = 1;
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 627, 0,
				   (char const *)
				   "sevent->ev_type == (((2) << 16) + 2)");
	tmp___0 = 0;
      }
    client = (ns_client_t *) sevent->ev_arg;
    if ((unsigned long) client != (unsigned long) ((void *) 0))
      {
	if (((isc__magic_t const *) client)->magic == 1314079587U)
	  {
	    tmp___1 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 629, 0,
				       (char const *)
				       "(((client) != ((void *)0)) && (((const isc__magic_t *)(client))->magic == ( ((\'N\') << 24 | (\'S\') << 16 | (\'C\') << 8 | (\'c\')))))");
	    tmp___1 = 0;
	  }
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 629, 0,
				   (char const *)
				   "(((client) != ((void *)0)) && (((const isc__magic_t *)(client))->magic == ( ((\'N\') << 24 | (\'S\') << 16 | (\'C\') << 8 | (\'c\')))))");
	tmp___1 = 0;
      }
    if ((unsigned long) task == (unsigned long) client->task)
      {
	tmp___2 = 1;
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 630, 0,
				   (char const *) "task == client->task");
	tmp___2 = 0;
      }
    if ((unsigned long) sevent == (unsigned long) client->sendevent)
      {
	tmp___3 = 1;
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 631, 0,
				   (char const *)
				   "sevent == client->sendevent");
	tmp___3 = 0;
      }
    ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
		   (char const *) "%s", "senddone");
    if (sevent->result != 0U)
      {
	tmp___4 = isc_result_totext (sevent->result);
	ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, -3,
		       (char const *) "error sending response: %s", tmp___4);
      }
    if (client->nsends > 0)
      {
	tmp___5 = 1;
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 643, 2,
				   (char const *) "client->nsends > 0");
	tmp___5 = 0;
      }
    client->nsends--;
    if ((unsigned long) client->tcpbuf != (unsigned long) ((void *) 0))
      {
	if ((client->attributes & 1U) != 0U)
	  {
	    tmp___6 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 647, 2,
				       (char const *)
				       "(((client)->attributes & 0x01) != 0)");
	    tmp___6 = 0;
	  }
	while (1)
	  {
	    isc__mem_put (client->mctx, (void *) client->tcpbuf, 65537U);
	    client->tcpbuf = (unsigned char *) ((void *) 0);
	    break;
	  }
	client->tcpbuf = (unsigned char *) ((void *) 0);
      }
    tmp___7 = exit_check (client);
    if (tmp___7)
      {
	return;
      }
    ns_client_next (client, 0U);
    return;
  }
}
static isc_result_t
client_sendpkg (ns_client_t * client, isc_buffer_t * buffer)
{
  struct in6_pktinfo *pktinfo;
  isc_result_t result;
  isc_region_t r;
  isc_sockaddr_t *address;
  isc_socket_t *socket___0;
  isc_netaddr_t netaddr;
  int match;
  unsigned int sockflags;
  isc_result_t tmp;
  {
    sockflags = 1U;
    if ((client->attributes & 1U) != 0U)
      {
	socket___0 = client->tcpsocket;
	address = (isc_sockaddr_t *) ((void *) 0);
      }
    else
      {
	socket___0 = client->udpsocket;
	address = &client->peeraddr;
	isc_netaddr_fromsockaddr (&netaddr,
				  (isc_sockaddr_t const *) (&client->
							    peeraddr));
	if ((unsigned long) ns_g_server->blackholeacl !=
	    (unsigned long) ((void *) 0))
	  {
	    tmp =
	      dns_acl_match (&netaddr, (dns_name_t *) ((void *) 0),
			     ns_g_server->blackholeacl, &ns_g_server->aclenv,
			     &match, (dns_aclelement_t **) ((void *) 0));
	    if (tmp == 0U)
	      {
		if (match > 0)
		  {
		    return (65604U);
		  }
	      }
	  }
	sockflags |= 2U;
      }
    if ((client->attributes & 4U) != 0U)
      {
	pktinfo = &client->pktinfo;
      }
    else
      {
	pktinfo = (struct in6_pktinfo *) ((void *) 0);
      }
    isc__buffer_usedregion (buffer, &r);
    ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
		   (char const *) "%s", "sendto");
    result =
      isc_socket_sendto2 (socket___0, &r, client->task, address, pktinfo,
			  client->sendevent, sockflags);
    if (result == 0U)
      {
	goto _L;
      }
    else
      {
	if (result == 53U)
	  {
	  _L:client->nsends++;
	    if (result == 0U)
	      {
		client_senddone (client->task,
				 (isc_event_t *) client->sendevent);
	      }
	    result = 0U;
	  }
      }
    return (result);
  }
}
void
ns_client_sendraw (ns_client_t * client, dns_message_t * message)
{
  isc_result_t result;
  unsigned char *data;
  isc_buffer_t buffer;
  isc_region_t r;
  isc_region_t *mr;
  unsigned char sendbuf[4096];
  int tmp;
  {
    if ((unsigned long) client != (unsigned long) ((void *) 0))
      {
	if (((isc__magic_t const *) client)->magic == 1314079587U)
	  {
	    tmp = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 778, 0,
				       (char const *)
				       "(((client) != ((void *)0)) && (((const isc__magic_t *)(client))->magic == ( ((\'N\') << 24 | (\'S\') << 16 | (\'C\') << 8 | (\'c\')))))");
	    tmp = 0;
	  }
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 778, 0,
				   (char const *)
				   "(((client) != ((void *)0)) && (((const isc__magic_t *)(client))->magic == ( ((\'N\') << 24 | (\'S\') << 16 | (\'C\') << 8 | (\'c\')))))");
	tmp = 0;
      }
    ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
		   (char const *) "%s", "sendraw");
    mr = dns_message_getrawmessage (message);
    if ((unsigned long) mr == (unsigned long) ((void *) 0))
      {
	result = 24U;
	goto done;
      }
    result =
      client_allocsendbuf (client, &buffer, (isc_buffer_t *) ((void *) 0),
			   mr->length, sendbuf, &data);
    if (result != 0U)
      {
	goto done;
      }
    isc__buffer_availableregion (&buffer, &r);
    result = isc_buffer_copyregion (&buffer, (isc_region_t const *) mr);
    if (result != 0U)
      {
	goto done;
      }
    (*(r.base + 0)) =
      (unsigned char) (((int) (client->message)->id >> 8) & 255);
    (*(r.base + 1)) = (unsigned char) ((int) (client->message)->id & 255);
    result = client_sendpkg (client, &buffer);
    if (result == 0U)
      {
	return;
      }
  done:if ((unsigned long) client->tcpbuf !=
	(unsigned long) ((void *) 0))
      {
	while (1)
	  {
	    isc__mem_put (client->mctx, (void *) client->tcpbuf, 65537U);
	    client->tcpbuf = (unsigned char *) ((void *) 0);
	    break;
	  }
	client->tcpbuf = (unsigned char *) ((void *) 0);
      }
    ns_client_next (client, result);
    return;
  }
}
static void
client_request (isc_task_t * task, isc_event_t * event)
{
  ns_client_t *client;
  isc_socketevent_t *sevent;
  isc_result_t result;
  isc_result_t sigresult;
  isc_buffer_t *buffer;
  isc_buffer_t tbuffer;
  dns_view_t *view;
  dns_rdataset_t *opt;
  isc_boolean_t ra;
  isc_netaddr_t netaddr;
  isc_netaddr_t destaddr;
  int match;
  dns_messageid_t id;
  unsigned int flags;
  isc_boolean_t notimp;
  int tmp;
  int tmp___0;
  int tmp___1;
  int tmp___2;
  int tmp___3;
  int tmp___4;
  int tmp___5;
  int tmp___6;
  int tmp___7;
  int tmp___8;
  int tmp___9;
  int tmp___10;
  isc_boolean_t tmp___11;
  char const *tmp___12;
  char *tmp___13;
  isc_result_t tmp___14;
  unsigned int version;
  int tmp___15;
  isc_boolean_t tmp___16;
  isc_boolean_t tmp___17;
  char classname[(int) sizeof ("CLASS65535")];
  isc_buffer_t b;
  isc_region_t *r;
  int tmp___18;
  char const *tmp___19;
  isc_result_t tmp___20;
  {
    if ((unsigned long) event != (unsigned long) ((void *) 0))
      {
	tmp = 1;
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 1077, 0,
				   (char const *) "event != ((void *)0)");
	tmp = 0;
      }
    client = (ns_client_t *) event->ev_arg;
    if ((unsigned long) client != (unsigned long) ((void *) 0))
      {
	if (((isc__magic_t const *) client)->magic == 1314079587U)
	  {
	    tmp___0 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 1079, 0,
				       (char const *)
				       "(((client) != ((void *)0)) && (((const isc__magic_t *)(client))->magic == ( ((\'N\') << 24 | (\'S\') << 16 | (\'C\') << 8 | (\'c\')))))");
	    tmp___0 = 0;
	  }
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 1079, 0,
				   (char const *)
				   "(((client) != ((void *)0)) && (((const isc__magic_t *)(client))->magic == ( ((\'N\') << 24 | (\'S\') << 16 | (\'C\') << 8 | (\'c\')))))");
	tmp___0 = 0;
      }
    if ((unsigned long) task == (unsigned long) client->task)
      {
	tmp___1 = 1;
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 1080, 0,
				   (char const *) "task == client->task");
	tmp___1 = 0;
      }
    if ((unsigned long) client->recursionquota ==
	(unsigned long) ((void *) 0))
      {
	tmp___2 = 1;
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 1084, 2,
				   (char const *)
				   "client->recursionquota == ((void *)0)");
	tmp___2 = 0;
      }
    if (client->state == ((client->attributes & 1U) != 0U))
      {
	tmp___3 = 3;
      }
    else
      {
	tmp___3 = 2;
      }
    if (tmp___3)
      {
	tmp___4 = 1;
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 1089, 2,
				   (char const *)
				   "client->state == (((client)->attributes & 0x01) != 0) ? 3 : 2");
	tmp___4 = 0;
      }
    if (event->ev_type == 131073U)
      {
	if ((client->attributes & 1U) != 0U)
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 1092, 2,
				       (char const *)
				       "!(((client)->attributes & 0x01) != 0)");
	    tmp___5 = 0;
	  }
	else
	  {
	    tmp___5 = 1;
	  }
	sevent = (isc_socketevent_t *) event;
	if ((unsigned long) sevent == (unsigned long) client->recvevent)
	  {
	    tmp___6 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 1094, 0,
				       (char const *)
				       "sevent == client->recvevent");
	    tmp___6 = 0;
	  }
	isc__buffer_init (&tbuffer, (void const *) sevent->region.base,
			  sevent->n);
	isc__buffer_add (&tbuffer, sevent->n);
	buffer = &tbuffer;
	result = sevent->result;
	if (result == 0U)
	  {
	    client->peeraddr = sevent->address;
	    client->peeraddr_valid = 1;
	  }
	if ((sevent->attributes & 1048576U) != 0U)
	  {
	    client->attributes |= 4U;
	    client->pktinfo = sevent->pktinfo;
	  }
	if ((sevent->attributes & 524288U) != 0U)
	  {
	    client->attributes |= 8U;
	  }
	client->nrecvs--;
      }
    else
      {
	if ((client->attributes & 1U) != 0U)
	  {
	    tmp___7 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 1111, 2,
				       (char const *)
				       "(((client)->attributes & 0x01) != 0)");
	    tmp___7 = 0;
	  }
	if (event->ev_type == 262151U)
	  {
	    tmp___8 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 1112, 0,
				       (char const *)
				       "event->ev_type == (((4) << 16) + 7)");
	    tmp___8 = 0;
	  }
	if ((unsigned long) event->ev_sender ==
	    (unsigned long) (&client->tcpmsg))
	  {
	    tmp___9 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 1113, 0,
				       (char const *)
				       "event->ev_sender == &client->tcpmsg");
	    tmp___9 = 0;
	  }
	buffer = &client->tcpmsg.buffer;
	result = client->tcpmsg.result;
	if (client->nreads == 1)
	  {
	    tmp___10 = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "client.c", 1116, 2,
				       (char const *) "client->nreads == 1");
	    tmp___10 = 0;
	  }
	client->nreads--;
      }
    tmp___11 = exit_check (client);
    if (tmp___11)
      {
	goto cleanup;
      }
    client->newstate = 4;
    client->state = client->newstate;
    isc_stdtime_get (&client->requesttime);
    client->now = client->requesttime;
    if (result != 0U)
      {
	if ((client->attributes & 1U) != 0U)
	  {
	    ns_client_next (client, result);
	  }
	else
	  {
	    if (result != 20U)
	      {
		tmp___12 = isc_result_totext (result);
		isc_log_write (ns_g_lctx, ns_g_categories + 1,
			       ns_g_modules + 1, -4,
			       (char const *)
			       "UDP client handler shutting down due to fatal receive error: %s",
			       tmp___12);
	      }
	    isc_task_shutdown (client->task);
	  }
	goto cleanup;
      }
    isc_netaddr_fromsockaddr (&netaddr,
			      (isc_sockaddr_t const *) (&client->peeraddr));
    if ((client->attributes & 1U) != 0U)
      {
	tmp___13 = "TCP";
      }
    else
      {
	tmp___13 = "UDP";
      }
    ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
		   (char const *) "%s request", tmp___13);
    if (!((client->attributes & 1U) != 0U))
      {
	if ((unsigned long) ns_g_server->blackholeacl !=
	    (unsigned long) ((void *) 0))
	  {
	    tmp___14 =
	      dns_acl_match (&netaddr, (dns_name_t *) ((void *) 0),
			     ns_g_server->blackholeacl, &ns_g_server->aclenv,
			     &match, (dns_aclelement_t **) ((void *) 0));
	    if (tmp___14 == 0U)
	      {
		if (match > 0)
		  {
		    ns_client_log (client, &dns_categories[2],
				   ns_g_modules + 1, 10,
				   (char const *) "blackholed UDP datagram");
		    ns_client_next (client, 0U);
		    goto cleanup;
		  }
	      }
	  }
      }
    if ((client->attributes & 8U) != 0U)
      {
	ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 2,
		       (char const *) "multicast request");
      }
    result = dns_message_peekheader (buffer, &id, &flags);
    if (result != 0U)
      {
	ns_client_next (client, result);
	goto cleanup;
      }
    if ((flags & 32768U) != 0U)
      {
	if ((client->attributes & 1U) != 0U)
	  {
	    ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
			   (char const *) "%s", "unexpected response");
	    ns_client_next (client, 196609U);
	    goto cleanup;
	  }
	else
	  {
	    dns_dispatch_importrecv (client->dispatch, event);
	    ns_client_next (client, 0U);
	    goto cleanup;
	  }
      }
    result = dns_message_parse (client->message, buffer, 0U);
    if (result != 0U)
      {
	ns_client_error (client, result);
	goto cleanup;
      }
    switch ((int) (client->message)->opcode)
      {
      case 0:;
      case 5:;
      case 4:
	notimp = 0;
	break;
      case 1:;
      default:
	notimp = 1;
	break;
      }
    (client->message)->rcode = 0;
    opt = dns_message_getopt (client->message);
    if ((unsigned long) opt != (unsigned long) ((void *) 0))
      {
	client->udpsize = opt->rdclass;
	if ((int) client->udpsize < 512)
	  {
	    client->udpsize = 512;
	  }
	client->extflags = (unsigned short) (opt->ttl & 65535U);
	result = client_addopt (client);
	if (result != 0U)
	  {
	    ns_client_error (client, result);
	    goto cleanup;
	  }
	version = (opt->ttl & 16711680U) >> 16;
	if (version != 0U)
	  {
	    ns_client_error (client, 196624U);
	    goto cleanup;
	  }
      }
    if ((int) (client->message)->rdclass == 0)
      {
	ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 1,
		       (char const *)
		       "message class could not be determined");
	ns_client_dumpmessage (client,
			       (char const *)
			       "message class could not be determined");
	if (notimp)
	  {
	    tmp___15 = 196612;
	  }
	else
	  {
	    tmp___15 = 196609;
	  }
	ns_client_error (client, (unsigned int) tmp___15);
	goto cleanup;
      }
    if ((int) (client->interface)->addr.type.sa.sa_family == 10)
      {
	if ((client->attributes & 4U) != 0U)
	  {
	    isc_netaddr_fromin6 (&destaddr,
				 (struct in6_addr const *) (&client->pktinfo.
							    ipi6_addr));
	  }
	else
	  {
	    isc_netaddr_any6 (&destaddr);
	  }
      }
    else
      {
	isc_netaddr_fromsockaddr (&destaddr,
				  (isc_sockaddr_t const
				   *) (&(client->interface)->addr));
      }
    view = ns_g_server->viewlist.head;
    while ((unsigned long) view != (unsigned long) ((void *) 0))
      {
	if ((int) (client->message)->rdclass == (int) view->rdclass)
	  {
	    goto _L;
	  }
	else
	  {
	    if ((int) (client->message)->rdclass == 255)
	      {
	      _L:tmp___16 =
		  allowed (&netaddr, view->matchclients);
		if (tmp___16)
		  {
		    tmp___17 = allowed (&destaddr, view->matchdestinations);
		    if (tmp___17)
		      {
			if ((flags & 256U) == 0U)
			  {
			    if (!view->matchrecursiveonly)
			      {
				dns_view_attach (view, &client->view);
				break;
			      }
			  }
			else
			  {
			    dns_view_attach (view, &client->view);
			    break;
			  }
		      }
		  }
	      }
	  }
	view = view->link.next;
      }
    if ((unsigned long) view == (unsigned long) ((void *) 0))
      {
	r = dns_message_getrawmessage (client->message);
	isc__buffer_init (&b, (void const *) r->base, r->length);
	isc__buffer_add (&b, r->length);
	dns_tsig_verify (&b, client->message,
			 (dns_tsig_keyring_t *) ((void *) 0),
			 (dns_tsig_keyring_t *) ((void *) 0));
	dns_rdataclass_format ((client->message)->rdclass, classname,
			       sizeof (classname));
	ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 1,
		       (char const *) "no matching view in class \'%s\'",
		       classname);
	ns_client_dumpmessage (client,
			       (char const *) "no matching view in class");
	if (notimp)
	  {
	    tmp___18 = 196612;
	  }
	else
	  {
	    tmp___18 = 196613;
	  }
	ns_client_error (client, (unsigned int) tmp___18);
	goto cleanup;
      }
    ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 5,
		   (char const *) "using view \'%s\'", view->name);
    sigresult = dns_message_checksig (client->message, client->view);
    client->signer = (dns_name_t *) ((void *) 0);
    dns_name_init (&client->signername, (unsigned char *) ((void *) 0));
    result = dns_message_signer (client->message, &client->signername);
    if (result == 0U)
      {
	ns_client_log (client, &dns_categories[2], ns_g_modules + 1, 3,
		       (char const *) "request has valid signature");
	client->signer = &client->signername;
      }
    else
      {
	if (result == 23U)
	  {
	    ns_client_log (client, &dns_categories[2], ns_g_modules + 1, 3,
			   (char const *) "request is not signed");
	  }
	else
	  {
	    if (result == 65591U)
	      {
		ns_client_log (client, &dns_categories[2], ns_g_modules + 1,
			       3,
			       (char const *)
			       "request is signed by a nonauthoritative key");
	      }
	    else
	      {
		tmp___19 = isc_result_totext (result);
		ns_client_log (client, &dns_categories[2], ns_g_modules + 1,
			       -4,
			       (char const *)
			       "request has invalid signature: %s", tmp___19);
		if ((int) (client->message)->tsigstatus == 17)
		  {
		    if (!((client->message)->opcode == 5U))
		      {
			ns_client_error (client, sigresult);
			goto cleanup;
		      }
		  }
		else
		  {
		    ns_client_error (client, sigresult);
		    goto cleanup;
		  }
	      }
	  }
      }
    ra = 0;
    if ((unsigned long) (client->view)->resolver !=
	(unsigned long) ((void *) 0))
      {
	if ((int) (client->view)->recursion == 1)
	  {
	    tmp___20 =
	      ns_client_checkacl (client,
				  (char const *) "recursion available:",
				  (client->view)->recursionacl, 1, 1);
	    if (tmp___20 == 0U)
	      {
		ra = 1;
	      }
	  }
      }
    if ((int) ra == 1)
      {
	client->attributes |= 2U;
      }
    switch ((int) (client->message)->opcode)
      {
      case 0:
	ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
		       (char const *) "%s", "query");
	ns_query_start (client);
	break;
      case 5:
	ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
		       (char const *) "%s", "update");
	ns_client_settimeout (client, 60U);
	ns_update_start (client, sigresult);
	break;
      case 4:
	ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
		       (char const *) "%s", "notify");
	ns_client_settimeout (client, 60U);
	ns_notify_start (client);
	break;
      case 1:
	ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
		       (char const *) "%s", "iquery");
	ns_client_error (client, 196612U);
	break;
      default:
	ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
		       (char const *) "%s", "unknown opcode");
	ns_client_error (client, 196612U);
      }
  cleanup:return;
  }
}
static void
client_read (ns_client_t * client)
{
  isc_result_t result;
  int tmp;
  int tmp___0;
  {
    ns_client_log (client, ns_g_categories + 1, ns_g_modules + 1, 3,
		   (char const *) "%s", "read");
    result =
      dns_tcpmsg_readmessage (&client->tcpmsg, client->task, &client_request,
			      (void *) client);
    if (result != 0U)
      {
	goto fail;
      }
    ns_client_settimeout (client, 30U);
    client->newstate = 3;
    client->state = client->newstate;
    if (client->nreads == 0)
      {
	tmp = 1;
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 1656, 2,
				   (char const *) "client->nreads == 0");
	tmp = 0;
      }
    if ((unsigned long) client->recursionquota ==
	(unsigned long) ((void *) 0))
      {
	tmp___0 = 1;
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "client.c", 1657, 2,
				   (char const *)
				   "client->recursionquota == ((void *)0)");
	tmp___0 = 0;
      }
    client->nreads++;
    return;
  fail:ns_client_next (client, result);
    return;
  }
}
