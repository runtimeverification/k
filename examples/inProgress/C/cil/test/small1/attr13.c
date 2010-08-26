//The following code occurs in linux-2.6.17.1 in drivers/char/ip2/i2pack.h:
typedef struct _i2DataHeader
{
    // For incoming data, indicates whether this is an ordinary packet or a
    // special one (e.g., hot key hit).
    unsigned i2sId : 2 __attribute__ ((__packed__));
};
