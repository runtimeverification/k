void code()
{
#if defined(__GNUC__) && defined(__i386__)
  asm("pxor %%mm6, %%mm6":);
  asm("pxor  %mm6,  %mm6" );
#endif
}
