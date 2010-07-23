// #define PRINT_ALL

extern int retval;
extern int printf(char*, ...);

void checkOffset(unsigned char * start, unsigned int size,
                 unsigned int expected_start,
                 unsigned int expected_width,
                 char *name) {
  int bits = 0;
  unsigned char *p = (unsigned char*)start;
  unsigned char c;
  
  // Advance past 0 bytes
  for(bits = 0; (! *p) && bits < 8 * size; bits += 8)
    p ++;
  
  c = *p ++; 

  if(bits >= 8 * size) {
    printf("Cannot find 1 bits in %s\n", name);
    retval = 1;
    return;
  }

  // Find the first bit = 1
  while(! (c & 1)) {
    c >>= 1; bits ++;
  }
  if(expected_start != bits) {
    printf("Error: Offset of %s is %d and I thought it was %d\n", name, bits,
           expected_start);
    retval = 1;
  }
#ifdef PRINT_ALL
  else {
    printf("Offset of %s is %d\n", name, expected_start);
  }
#endif    
  expected_start = bits;

  // Now find the end
  while(1) {
    while(c & 1) { c >>= 1; bits ++; } 
    if((bits & 7) == 0) {
      if(bits == 8 * size) break;
      c = * p ++;
      if(! (c & 1)) break;
    } else
      break;
  }
  if(bits - expected_start != expected_width) {
    int i;
    printf("Error: Width of %s is %d and I thought it was %d.\n", name,
           bits - expected_start, expected_width);
    retval = 1;
    for(i=0;i<size;i++) {
      printf("[%d] = 0x%02x,", i, start[i]);
    }
    printf("\n");
  }
  
}

void checkSizeOf(unsigned int size,
                 unsigned int expected, char *name) {
  if(expected & 7) {
    printf("Expected %d bits for the length of %s. Should be 8x\n",
           expected, name);
    retval = 1;
  }
  if(size != expected / 8) {
    printf("Error: Size of %s is %d and I thought it was %d\n", name,
           size, expected / 8);
    retval = 1;
  }
#ifdef PRINT_ALL
  else {
    printf("Sizeof %s is %d\n", name, expected / 8);
  }
#endif    
}


