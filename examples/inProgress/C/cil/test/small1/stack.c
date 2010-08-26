

/* struct pointers { */
/*   char* gp; */
/*   char* gp2; */
/*   char** gpp; */
/*   char** gpp2; */
/* }; */

struct s {
  int i;
  int i2;
};

struct s global;

int main() {
  char* __SEQ * gp = 0;
  char* __SEQ * gp2 = 0;
  char* __SEQ * __SEQ * gpp = 0;
  int (* funcPtr)() = 0;

  struct s stack;
  int** p_stackField;
  int** p_globalField;

  char str[52];
  char* p = *gp; //no

  *gp2 = str;  //yes
  *gp = p;    //no
  *gpp = &p;  //yes
  *gpp = *gpp;  //yes
  *gpp = gp; //no

  *gpp = 0; //no
  funcPtr = main; //no

  *p_stackField = &stack.i2;   //yes
  *p_globalField = &global.i2; //no

  return 0;
}
