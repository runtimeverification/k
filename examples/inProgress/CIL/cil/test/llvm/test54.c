typedef struct {
    int *value;
} precisionType;

typedef precisionType *precision;



void pnorm(u)
    precision u;
{
    int *uPtr;

   uPtr = u->value;
   do {
      if (*--uPtr != 0) break;
   } while (uPtr > u->value);
}

int main(int argc, char **argv)
{
  return 0;
}
