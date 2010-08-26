extern void error(int status , int errnum , const char *  format , ...)
  __attribute__((__format__(__printf__, 3, 4))) ;


static void parse_group(const char *  name) {
  if(0) error(1, 0, gettext("invalid group name %s"), quote(name));
}


int main(int argc , char *  *  argv ) {
  return 0;
}

