extern __inline   double     atan   ( double  __x)  	{
  register  double  __result;
  __asm __volatile__ ( "fld1; fpatan"
                       : "=t" (__result) :
                       "0" (__x)
                       : "st(1)"  );
  return __result;
}
