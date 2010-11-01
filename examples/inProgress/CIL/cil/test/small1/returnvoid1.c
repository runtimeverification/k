#include <stdio.h>
#include <stdlib.h>

#define PAGE_SIZE 512;
#define FREAK() printf("wow.")

typedef struct b_data_t {
  int node_boot_start;
  int node_low_pfn;
} bootmem_data_t;

typedef struct pg_d_t {
  struct b_data_t* bdata;
} pg_data_t;

static void free_bootmem_core(bootmem_data_t *bdata, unsigned long addr, unsigned long size) {
  unsigned long i;
  unsigned long start;
  unsigned long sidx;
  unsigned long eidx, end;
  eidx = (addr + size - bdata->node_boot_start)/PAGE_SIZE;
  end = (addr + size)/PAGE_SIZE;
  
  if (!size) FREAK();
  if (end > bdata->node_low_pfn)
    FREAK();
  
}

void free_bootmem_node(pg_data_t *pgdat, unsigned long physaddr, unsigned long size) {
  return(free_bootmem_core(pgdat->bdata, physaddr, size));
}

int main(int charc, char ** argv) {
  return 0;
}
