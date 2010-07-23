#include "testharness.h"

typedef struct _NDIS30_MINIPORT_CHARACTERISTICS
{
    int                       MajorNdisVersion;
    int                       MinorNdisVersion;
    int                       Filler;
    int                       Reserved;
    int    CheckForHangHandler;
    int    DisableInterruptHandler;
    int    EnableInterruptHandler;
    int    HaltHandler;
    int    HandleInterruptHandler;
    int    InitializeHandler;
    int    ISRHandler;
    int    QueryInformationHandler;
    int    ReconfigureHandler;
    int     ResetHandler;
    union
    {
        int          SendHandler;
        int          WanSendHandler;
    };
    int              SetInformationHandler;
    union
    {
        int TransferDataHandler;
        int WanTransferDataHandler;
    };
} NDIS30_MINIPORT_CHARACTERISTICS;

typedef struct _NDIS40_MINIPORT_CHARACTERISTICS {
    NDIS30_MINIPORT_CHARACTERISTICS;
    int      ReturnPacketHandler;
    int      SendPacketsHandler;
    int      AllocateCompleteHandler;

} NDIS40_MINIPORT_CHARACTERISTICS;

typedef struct _NDIS50_MINIPORT_CHARACTERISTICS
{
    NDIS40_MINIPORT_CHARACTERISTICS;
    
    int  CoCreateVcHandler;
    int  CoDeleteVcHandler;
    int  CoActivateVcHandler;
    int  CoDeactivateVcHandler;
    int  CoSendPacketsHandler;
    int  CoRequestHandler;
} NDIS50_MINIPORT_CHARACTERISTICS;

typedef struct _NDIS51_MINIPORT_CHARACTERISTICS {
    NDIS50_MINIPORT_CHARACTERISTICS;
    int  CancelSendPacketsHandler;
    int  PnPEventNotifyHandler;
    int  AdapterShutdownHandler;
    int  Reserved1;
    int  Reserved2;
    int  Reserved3;
    int  Reserved4;
} NDIS51_MINIPORT_CHARACTERISTICS;

typedef struct _NDIS51_MINIPORT_CHARACTERISTICS NDIS_MINIPORT_CHARACTERISTICS;


int main() {
    NDIS_MINIPORT_CHARACTERISTICS   m;

    // Fill the object with 1,2,...
    m.MajorNdisVersion          = 1;
    m.MinorNdisVersion          = 2;
    m.Filler                    = 3;
    m.Reserved                  = 4;

    m.CheckForHangHandler = 5;
    m.DisableInterruptHandler = 6;
    m.EnableInterruptHandler = 7;
    m.HaltHandler = 8;
    m.HandleInterruptHandler = 9;
    m.InitializeHandler = 10;
    m.ISRHandler = 11;
    m.QueryInformationHandler = 12;
    m.ReconfigureHandler = 13;
    m.ResetHandler = 14;
    
    m.SendHandler = 15;
    if(m.WanSendHandler != 15) E(1);

    m.SetInformationHandler = 16;
    m.TransferDataHandler = 17;
    if(m.WanTransferDataHandler != 17) E(2);

    // These are from NDIS40
    m.ReturnPacketHandler = 18;
    m.SendPacketsHandler = 19;
    m.AllocateCompleteHandler = 20;
    

    // These are from NDIS50
    m.CoCreateVcHandler = 21;
    m.CoDeleteVcHandler = 22;
    m.CoActivateVcHandler = 23;
    m.CoDeactivateVcHandler = 24;
    m.CoSendPacketsHandler = 25;
    m.CoRequestHandler = 26;

    // These are from NDIS51
    m.CancelSendPacketsHandler = 27;
    m.PnPEventNotifyHandler = 28;
    m.AdapterShutdownHandler = 29;
    m.Reserved1 = 30;
    m.Reserved2 = 31;
    m.Reserved3 = 32;
    m.Reserved4 = 33;


    // Now go and check the we have initialized properly
    {
      int i;
      for(i=0;i<sizeof(m) / sizeof(int); i++) {
        if(((int*)&m)[i] != i + 1) {
          printf("The %dth word is %d\n", i, ((int*)&m)[i]);
          E(3);
        }
      }
    }
    SUCCESS;
}
