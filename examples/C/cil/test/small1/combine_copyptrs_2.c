struct true_type
{
};
typedef struct true_type ret_true_type;
typedef char otherChar;
typedef char value_type;
typedef ret_true_type Type;
struct cc
{
};
__inline static char
  *copy_aux (char
	     *first, char *last, char *result, struct true_type const *_6);
__inline static struct cc
  isOkToMemCpy (value_type * __T136310140, value_type * __T136310232) 
{
  struct cc foo;
  return foo;
}
__inline static char *copyptrs (char *__5338_43___first,
				char *__5338_63___last,
				char *__5338_83___result,
				struct true_type const *__T136310416);
__inline static Type has_trivial (void)
{
  Type foo;
  return foo;
}
__inline static char *
copy_aux (char *first, char *last, char *result, struct true_type const *_6)
{
  Type __T136310508;
  char *tmp;
  {
    isOkToMemCpy ((value_type *) 0, (value_type *) 0);
    has_trivial ();
    tmp =
      copyptrs (first, last, result,
		(struct true_type const *) (&__T136310508));
    return (tmp);
  }
}
__inline static char *
copyptrs (char *__5338_43___first, char *__5338_63___last,
	  char *__5338_83___result, struct true_type const *_6)
{
}
__inline static struct cc
  isOkToMemCpy___0 (value_type * __T144603992, value_type * __T144604084);
__inline static otherChar *copyptrs___0 (char *first,
					 char *last,
					 otherChar * result,
					 struct true_type const *_8);
__inline static Type has_trivial___0 (void)
{
  Type *pFoo;
  return *pFoo;
}
__inline static otherChar *
copy_aux___0 (char
	      *first,
	      char *last, otherChar * result, struct true_type const *_8)
{
  Type __T144604360;
  otherChar *tmp;
  {
    isOkToMemCpy___0 ((value_type *) 0, (value_type *) 0);
    has_trivial___0 ();
    tmp =
      copyptrs___0 (first, last, result,
		    (struct true_type const *) (&__T144604360));
    return (tmp);
  }
}
__inline static otherChar *
copyptrs___0 (char *__8528_43___first, char *__8528_63___last,
	      otherChar * __8528_83___result, struct true_type const *_8)
{
}

int main()
{
  copyptrs(0,0,0,0);
  return 0;
}
