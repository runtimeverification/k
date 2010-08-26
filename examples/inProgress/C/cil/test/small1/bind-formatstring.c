/* Weimer: bind-based testcase for "Bug: handleFormatString" 
 * Look for:
 * input.c:222: Bug: handleFormatString
 * Markptr: instruction error (Errormsg.Error) at bind-formatstring.c:227
 * run: ccured.asm.exe --curetype infer --assumePrintf input.c
 */
typedef enum __anonenum_isc_boolean_t_16 isc_boolean_t;
typedef enum __anonenum_isc_assertiontype_t_17 isc_assertiontype_t;
typedef struct isc_log isc_log_t;
typedef struct isc_mem isc_mem_t;
typedef struct isc_netaddr isc_netaddr_t;
typedef unsigned int isc_result_t;
typedef struct dns_acl dns_acl_t;
typedef struct dns_aclelement dns_aclelement_t;
typedef struct dns_name dns_name_t;
typedef enum __anonenum_dns_aclelemettype_t_53 dns_aclelemettype_t;
typedef struct dns_aclipprefix dns_aclipprefix_t;
struct dns_aclipprefix
{
  isc_netaddr_t address;
  unsigned int prefixlen;
};
union __anonunion_u_54
{
  dns_aclipprefix_t ip_prefix;
  dns_name_t keyname;
  dns_acl_t *nestedacl;
};
struct dns_aclelement
{
  dns_aclelemettype_t type;
  isc_boolean_t negative;
  union __anonunion_u_54 u;
};
struct dns_acl
{
  dns_aclelement_t *elements;
  unsigned int length;
};
typedef struct cfg_type cfg_type_t;
typedef struct cfg_obj cfg_obj_t;
typedef struct cfg_listelt cfg_listelt_t;
typedef struct ns_aclconfctx ns_aclconfctx_t;
void (*isc_assertion_failed) (char const *, int, isc_assertiontype_t,
			      char const *);

isc_log_t *dns_lctx;
void (cfg_obj_log) (cfg_obj_t * obj, isc_log_t * lctx, int level,
		    char const *fmt, ...);
cfg_type_t cfg_type_keyref;
isc_result_t
ns_acl_fromconfig (cfg_obj_t * caml, cfg_obj_t * cctx, ns_aclconfctx_t * ctx,
		   isc_mem_t * mctx, dns_acl_t ** target)
{
  isc_result_t result;
  unsigned int count;
  dns_acl_t *dacl;
  dns_aclelement_t *de;
  cfg_listelt_t *elt;
  int tmp;
  cfg_obj_t *ce;
  cfg_obj_t *tmp___0;
  isc_boolean_t tmp___1;
  char *name;
  char *tmp___2;
  int tmp___3;
  int tmp___4;
  int tmp___5;
  int tmp___6;
  isc_boolean_t tmp___7;
  isc_boolean_t tmp___8;
  isc_boolean_t tmp___9;
  isc_boolean_t tmp___10;
  {
    dacl = (dns_acl_t *) ((void *) 0);
    if ((unsigned long) target != (unsigned long) ((void *) 0))
      {
	if ((unsigned long) (*target) == (unsigned long) ((void *) 0))
	  {
	    tmp = 1;
	  }
	else
	  {
	    ((*isc_assertion_failed)) ((char const *) "aclconf.c", 148, 0,
				       (char const *)
				       "target != ((void *)0) && *target == ((void *)0)");
	    tmp = 0;
	  }
      }
    else
      {
	((*isc_assertion_failed)) ((char const *) "aclconf.c", 148, 0,
				   (char const *)
				   "target != ((void *)0) && *target == ((void *)0)");
	tmp = 0;
      }
    count = 0U;
    elt = cfg_list_first (caml);
    while ((unsigned long) elt != (unsigned long) ((void *) 0))
      {
	count++;
	elt = cfg_list_next (elt);
      }
    result = dns_acl_create (mctx, (int) count, &dacl);
    if (result != 0U)
      {
	return (result);
      }
    de = dacl->elements;
    elt = cfg_list_first (caml);
    while ((unsigned long) elt != (unsigned long) ((void *) 0))
      {
	tmp___0 = cfg_listelt_value (elt);
	ce = tmp___0;
	tmp___1 = cfg_obj_istuple (ce);
	if (tmp___1)
	  {
	    ce = cfg_tuple_get (ce, (char const *) "value");
	    de->negative = 1;
	  }
	else
	  {
	    de->negative = 0;
	  }
	tmp___10 = cfg_obj_isnetprefix (ce);
	if (tmp___10)
	  {
	    de->type = 0;
	    cfg_obj_asnetprefix (ce, &de->u.ip_prefix.address,
				 &de->u.ip_prefix.prefixlen);
	  }
	else
	  {
	    tmp___9 =
	      cfg_obj_istype (ce, (cfg_type_t const *) (&cfg_type_keyref));
	    if (tmp___9)
	      {
		de->type = 1;
		dns_name_init (&de->u.keyname,
			       (unsigned char *) ((void *) 0));
		result = convert_keyname (ce, mctx, &de->u.keyname);
		if (result != 0U)
		  {
		    goto cleanup;
		  }
	      }
	    else
	      {
		tmp___8 = cfg_obj_islist (ce);
		if (tmp___8)
		  {
		    de->type = 2;
		    result =
		      ns_acl_fromconfig (ce, cctx, ctx, mctx,
					 &de->u.nestedacl);
		    if (result != 0U)
		      {
			goto cleanup;
		      }
		  }
		else
		  {
		    tmp___7 = cfg_obj_isstring (ce);
		    if (tmp___7)
		      {
			tmp___2 = cfg_obj_asstring (ce);
			name = tmp___2;
			tmp___6 =
			  strcasecmp ((char const *) name,
				      (char const *) "localhost");
			if (tmp___6 == 0)
			  {
			    de->type = 3;
			  }
			else
			  {
			    tmp___5 =
			      strcasecmp ((char const *) name,
					  (char const *) "localnets");
			    if (tmp___5 == 0)
			      {
				de->type = 4;
			      }
			    else
			      {
				tmp___4 =
				  strcasecmp ((char const *) name,
					      (char const *) "any");
				if (tmp___4 == 0)
				  {
				    de->type = 5;
				  }
				else
				  {
				    tmp___3 =
				      strcasecmp ((char const *) name,
						  (char const *) "none");
				    if (tmp___3 == 0)
				      {
					de->type = 5;
					if (de->negative)
					  {
					    de->negative = 0;
					  }
					else
					  {
					    de->negative = 1;
					  }
				      }
				    else
				      {
					de->type = 2;
					result =
					  convert_named_acl (ce, cctx, ctx,
							     mctx,
							     &de->u.
							     nestedacl);
					if (result != 0U)
					  {
					    goto cleanup;
					  }
				      }
				  }
			      }
			  }
		      }
		    else
		      {
			cfg_obj_log (ce, dns_lctx, -3,
				     (char const *)
				     "address match list contains unsupported element type");
			result = 25U;
			goto cleanup;
		      }
		  }
	      }
	  }
	de++;
	dacl->length++;
	elt = cfg_list_next (elt);
      }
    (*target) = dacl;
    return (0U);
  cleanup:dns_acl_detach (&dacl);
    return (result);
  }
}
