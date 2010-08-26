//Make sure we parse 1UL in attributs

//from linux-2.6.17.1/kernel/power/power.h.   
struct swsusp_info {
  unsigned int version_code;
  unsigned long num_physpages;
  int cpus;
  unsigned long image_pages;
  unsigned long pages;
  unsigned long size;
} __attribute__((aligned((1UL << 12))));

struct swsusp_info global;

