#include <stdio.h>
#include <stddef.h>
#include <sys/stat.h>

typedef struct uri_components {
    /*
    char *  scheme ;
    char *  hostinfo ;
    char *  user ;
    char *  password ;
    char *  hostname ;
    char *  port_str ;
    char *  path ;
    char *  query ;
    char *  fragment ;
    */
    void *  hostent ;
    unsigned short port ;
    unsigned int is_initialized : 1 ;
    unsigned int dns_looked_up : 1 ;
    unsigned int dns_resolved : 1 ;
} uri_components;

/*
enum proxyreqtype {
    NOT_PROXY = 0,
    STD_PROXY = 1,
    PROXY_PASS = 2,  
};
*/

typedef struct request_rec {
    /*
   void *  pool ;
   void *  connection ;
   void *  server ;
   void *  next ;
   void *  prev ;
   void *  main ;
   char *  the_request ;
   int assbackwards ;
   enum proxyreqtype proxyreq ;
   int header_only ;
   char *  protocol ;
   int proto_num ;
   char *  hostname ;
   long request_time ;
   char *  status_line ;
   int status ;
   char *  method ;
   int method_number ;
   int allowed ;
   int sent_bodyct ;
   long bytes_sent ;
   long mtime ;
   int chunked ;
   int byterange ;
   char *  boundary ;
   char *  range ;
   long clength ;
   long remaining ;
   long read_length ;
   int read_body ;
   int read_chunked ;
   unsigned int expecting_100 ;
   void *  headers_in ;
   void *  headers_out ;
   void *  err_headers_out ;
   void *  subprocess_env ;
   void *  notes ;
   char *  content_type ;
   char *  handler ;
   char *  content_encoding ;
   char *  content_language ;
   void *  content_languages ;
   char *  vlist_validator ;
   int no_cache ;
   int no_local_copy ;
   char *  unparsed_uri ;
   char *  uri ;
   char *  filename ;
   char *  path_info ;
   char *  args ;
   struct stat finfo ;
   */
   uri_components parsed_uri ;
   void *  per_dir_config ;
   /*
   void *  request_config ;
   void *  htaccess ;
   char *  case_preserved_filename ;
   */
} request_rec;

int main() {
    request_rec r;
    void **offset;
    long diff;

    offset = &(r.per_dir_config); 

    diff = ((long) offset) - ((long)&r);

    printf("offset is %ld (and should be 8 with gcc version 2.95.3 19991030 (prerelease))\n", diff);
    return 0;
}
