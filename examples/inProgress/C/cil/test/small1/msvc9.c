
typedef struct _BUSENUM_PLUGIN_HARDWARE
{
    int Size;
    #pragma warning(disable:4200)  // nonstandard extension used
    int HardwareIDs[];
    #pragma warning(default:4200)  // nonstandard extension used

} BUSENUM_PLUGIN_HARDWARE, *PBUSENUM_PLUGIN_HARDWARE;

typedef struct _UNICODE_STRING {
  short Length;
  short MaximumLength;
  char * Buffer;
} UNICODE_STRING;

void foo() {
  int param;
  
  char buffer_buffer[80]; __pragma(warning(disable:4221)) __pragma(warning(disable:4204)) UNICODE_STRING buffer = { 0, 80 * sizeof(char) , buffer_buffer } __pragma(warning(default:4221)) __pragma(warning(default:4204));

  (param);             
}


#ifdef _MSVC
typedef unsigned __int64 ULONGLONG;

int
RtlIntToULongLong(
         int iOperand,
         ULONGLONG* pullResult)
{
  int status = ((int)0xC0000095L);
  *pullResult = (0xffffffffffffffffui64);
  
  return status;
}
#endif
