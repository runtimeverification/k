#include "testharness.h"

typedef struct _GUID {  // #line 17 "C:/ntddk/inc/guiddef.h"
  unsigned long Data1 ;
  unsigned short Data2 ;
  unsigned short Data3 ;
  unsigned char Data4[8] ;
} GUID ;

// #line 37 "C:/ntddk/inc/ntddpar.h"
extern const GUID __declspec(selectany) GUID_PARALLEL_DEVICE = {0x97F76EF0,
  0xF883, 0x11D0, {0xAF, 0x1F, 0x00, 0x00, 0xF8, 0x00, 0x84, 0x5C}};
extern const GUID __declspec(selectany) GUID_PARCLASS_DEVICE = {0x811FC6A5,
  0xF728, 0x11D0, {0xA5, 0x37, 0x00, 0x00, 0xF8, 0x75, 0x3E, 0xD1}};

typedef int NTSTATUS;
typedef void *PDEVICE_OBJECT;
typedef void *PUNICODE_STRING;

/* __declspec(dllimport) */ NTSTATUS __stdcall 
IoRegisterDeviceInterface(PDEVICE_OBJECT PhysicalDeviceObject , 
    const GUID *  InterfaceClassGuid , 
    PUNICODE_STRING ReferenceString , 
    PUNICODE_STRING SymbolicLinkName ) {
  if (InterfaceClassGuid->Data1 != 0x97F76EF0) {
    E(1);
  } 
  return 0; 
}

int main() {
  NTSTATUS status;

  // #line 470 "pnp.c" of the parport device driver
  status = IoRegisterDeviceInterface(0, &GUID_PARALLEL_DEVICE, 0, 0); 

  SUCCESS; 
}
