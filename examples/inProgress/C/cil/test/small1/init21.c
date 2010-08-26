#include "testharness.h"

//Linux: sound/usb/usbaudio.c
typedef struct snd_usb_audio_quirk snd_usb_audio_quirk_t;
typedef struct snd_usb_midi_endpoint_info snd_usb_midi_endpoint_info_t;

enum quirk_type {
 QUIRK_IGNORE_INTERFACE,
 QUIRK_COMPOSITE,
 QUIRK_MIDI_STANDARD_INTERFACE,
 QUIRK_MIDI_FIXED_ENDPOINT,
 QUIRK_MIDI_YAMAHA,
 QUIRK_MIDI_MIDIMAN,
 QUIRK_MIDI_NOVATION,
 QUIRK_MIDI_RAW,
 QUIRK_MIDI_EMAGIC,
 QUIRK_MIDI_MIDITECH,
 QUIRK_AUDIO_STANDARD_INTERFACE,
 QUIRK_AUDIO_FIXED_ENDPOINT,
 QUIRK_AUDIO_EDIROL_UA700_UA25,
 QUIRK_AUDIO_EDIROL_UA1000,

 QUIRK_TYPE_COUNT
};

enum sndrv_pcm_format {
 SNDRV_PCM_FORMAT_S8 = 0,
 SNDRV_PCM_FORMAT_U8,
 SNDRV_PCM_FORMAT_S16_LE,
 SNDRV_PCM_FORMAT_S16_BE,
 SNDRV_PCM_FORMAT_U16_LE,
 SNDRV_PCM_FORMAT_U16_BE,
 SNDRV_PCM_FORMAT_S24_LE,
 SNDRV_PCM_FORMAT_S24_BE,
 SNDRV_PCM_FORMAT_U24_LE,
 SNDRV_PCM_FORMAT_U24_BE,
 SNDRV_PCM_FORMAT_S32_LE,
 SNDRV_PCM_FORMAT_S32_BE,
 SNDRV_PCM_FORMAT_U32_LE,
 SNDRV_PCM_FORMAT_U32_BE,
 SNDRV_PCM_FORMAT_FLOAT_LE,
 SNDRV_PCM_FORMAT_FLOAT_BE,
 SNDRV_PCM_FORMAT_FLOAT64_LE,
 SNDRV_PCM_FORMAT_FLOAT64_BE,
 SNDRV_PCM_FORMAT_IEC958_SUBFRAME_LE,
 SNDRV_PCM_FORMAT_IEC958_SUBFRAME_BE,
 SNDRV_PCM_FORMAT_MU_LAW,
 SNDRV_PCM_FORMAT_A_LAW,
 SNDRV_PCM_FORMAT_IMA_ADPCM,
 SNDRV_PCM_FORMAT_MPEG,
 SNDRV_PCM_FORMAT_GSM,
 SNDRV_PCM_FORMAT_SPECIAL = 31,
 SNDRV_PCM_FORMAT_S24_3LE = 32,
 SNDRV_PCM_FORMAT_S24_3BE,
 SNDRV_PCM_FORMAT_U24_3LE,
 SNDRV_PCM_FORMAT_U24_3BE,
 SNDRV_PCM_FORMAT_S20_3LE,
 SNDRV_PCM_FORMAT_S20_3BE,
 SNDRV_PCM_FORMAT_U20_3LE,
 SNDRV_PCM_FORMAT_U20_3BE,
 SNDRV_PCM_FORMAT_S18_3LE,
 SNDRV_PCM_FORMAT_S18_3BE,
 SNDRV_PCM_FORMAT_U18_3LE,
 SNDRV_PCM_FORMAT_U18_3BE,
 SNDRV_PCM_FORMAT_LAST = SNDRV_PCM_FORMAT_U18_3BE,


 SNDRV_PCM_FORMAT_S16 = SNDRV_PCM_FORMAT_S16_LE,
 SNDRV_PCM_FORMAT_U16 = SNDRV_PCM_FORMAT_U16_LE,
 SNDRV_PCM_FORMAT_S24 = SNDRV_PCM_FORMAT_S24_LE,
 SNDRV_PCM_FORMAT_U24 = SNDRV_PCM_FORMAT_U24_LE,
 SNDRV_PCM_FORMAT_S32 = SNDRV_PCM_FORMAT_S32_LE,
 SNDRV_PCM_FORMAT_U32 = SNDRV_PCM_FORMAT_U32_LE,
 SNDRV_PCM_FORMAT_FLOAT = SNDRV_PCM_FORMAT_FLOAT_LE,
 SNDRV_PCM_FORMAT_FLOAT64 = SNDRV_PCM_FORMAT_FLOAT64_LE,
 SNDRV_PCM_FORMAT_IEC958_SUBFRAME = SNDRV_PCM_FORMAT_IEC958_SUBFRAME_LE,
};


struct snd_usb_audio_quirk {
 const char *vendor_name;
 const char *product_name;
 short ifnum;
  short type;
 const void *data;
};

struct snd_usb_midi_endpoint_info {
 char out_ep;
 char out_interval;
 char in_ep;
 char in_interval;
 short out_cables;
 short in_cables;
};



struct usb_device_id {

 short match_flags;


 short idVendor;
 short idProduct;
 short bcdDevice_lo;
 short bcdDevice_hi;


 char bDeviceClass;
 char bDeviceSubClass;
 char bDeviceProtocol;


 char bInterfaceClass;
 char bInterfaceSubClass;
 char bInterfaceProtocol;


 unsigned long driver_info;
};

struct audioformat {
  //struct list_head list;
 int format;
 unsigned int channels;
 unsigned int fmt_type;
 unsigned int frame_size;
 int iface;
 unsigned char altsetting;
 unsigned char altset_idx;
 unsigned char attributes;
 unsigned char endpoint;
 unsigned char ep_attr;
 unsigned int maxpacksize;
 unsigned int rates;
 unsigned int rate_min, rate_max;
 unsigned int nr_rates;
 unsigned int *rate_table;
};


static struct usb_device_id usb_audio_ids [] = {
{ .match_flags = (0x0001 | 0x0002), 
  .idVendor = (0x0499), .idProduct = (0x1000), 
  .driver_info = (unsigned long) & (const snd_usb_audio_quirk_t)
                                    { .vendor_name = "Yamaha", 
                                      .product_name = "UX256", 
                                      .ifnum = -1, 
                                      .type = 1 } 
},

{
 .match_flags = (0x0001 | 0x0002), .idVendor = (0x0582), .idProduct = (0x0000),
 .driver_info = (unsigned long) & (const snd_usb_audio_quirk_t) {
  .vendor_name = "Roland",
  .product_name = "UA-100",
  .ifnum = -1,
  .type = QUIRK_COMPOSITE,
  .data = (const snd_usb_audio_quirk_t[]) {
   {
    .ifnum = 0,
    .type = QUIRK_AUDIO_FIXED_ENDPOINT,
    .data = & (const struct audioformat) {
     .format = SNDRV_PCM_FORMAT_S16_LE,
     .channels = 4,
     .iface = 0,
     .altsetting = 1,
     .altset_idx = 1,
     .attributes = 0,
     .endpoint = 0x01,
     .ep_attr = 0x09,
     .rates = (1<<30),
     .rate_min = 44100,
     .rate_max = 44100,
    }
   },
   {
    .ifnum = 1,
    .type = QUIRK_AUDIO_FIXED_ENDPOINT,
    .data = & (const struct audioformat) {
     .format = SNDRV_PCM_FORMAT_S16_LE,
     .channels = 2,
     .iface = 1,
     .altsetting = 1,
     .altset_idx = 1,
     .attributes = 0x80,
     .endpoint = 0x81,
     .ep_attr = 0x05,
     .rates = (1<<30),
     .rate_min = 44100,
     .rate_max = 44100,
    }
   },
   {
    .ifnum = 2,
    .type = QUIRK_MIDI_FIXED_ENDPOINT,
    .data = & (const snd_usb_midi_endpoint_info_t) {
     .out_cables = 0x0007,
     .in_cables = 0x0007
    }
   },
   {
    .ifnum = -1
   }
  }
 }
},
{ }
} ;


struct foo{ int x; int y; const void* p; };

//struct foo glb = { .x = 4, .y = (int) & (struct foo){ .x = 1, .y = 2 } };

int main() {
  //  struct foo* p = & (struct foo){ .x = 1, .y = 2 };
  //  return p->x;
  snd_usb_audio_quirk_t* driver_info = (snd_usb_audio_quirk_t*)
    (usb_audio_ids[1].driver_info);
  if (((snd_usb_midi_endpoint_info_t*)((snd_usb_audio_quirk_t*)driver_info->data)[2].data)->out_cables != 7) E(3);
  if (((snd_usb_audio_quirk_t*)driver_info->data)[3].ifnum
      != -1) E(4);

  SUCCESS;
}
