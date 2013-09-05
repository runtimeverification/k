#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <limits.h>
#include "sdf-wrapper.h"

// #define DEBUG(...) fprintf(stderr, __VA_ARGS__)
#define DEBUG(...)

/*
 read a length-prefixed string of bytes
 expects a positive 32-bit big-endian integer and that many bytes futher data.
 puts length in len and returns a pointer to a newly allocated array
   of len+1 bytes including the data (which might contain embedded NULLs)
   plus a terminating null


 on various error condtiions returns NULL and sets *len negative.
 on EOF before first byte set *len to -1,
 on EOF later sets *len to -2,
 on other errors returns -3.
*/
char* recv_string(int* len) {
  unsigned int inputlen;
  int i;
  int c = getc(stdin);
  DEBUG("Got byte %d\n", c);
  if (c == EOF) {
    // EOF at start, tell caller
    *len = -1;
    return NULL; 
  }
  inputlen = c;
  DEBUG("Got first byte of string len\n");
 
  for (i = 0; i < 3; ++i) {
    c = getc(stdin);
    DEBUG("Got byte %d\n", c);
    if (c == EOF) {
      // EOF during header.
      *len = -2;
      return NULL;
    }
    inputlen *= 256;
    inputlen += c;
  }
  DEBUG("Got string len %u\n", inputlen);

  if (inputlen > INT_MAX) {
    // invalid length
    *len = -3;
    return NULL;
  }

  *len = inputlen;

  char *data = malloc(inputlen+1);
  if (!data) {
    // malloc failed
    *len = -3;
    return NULL;
  }
  int got = 0;
  while (got < inputlen) {
    DEBUG("Waiting for data\n");
    ssize_t received = fread(data+got, 1, inputlen-got, stdin);
    if (received == 0) {
      // EOF during data.
      *len = -2;
      return NULL;
    }
    if (received == -1) {
      // error reading data!
      *len = -3;
      return NULL;
    }
    got += received;
    DEBUG("Got %d bytes, have %d of %d remain\n", received, got, inputlen);
  }
  data[inputlen] = 0;

  return data;
}

/* process a request,
   exit process with exit code 0 on EOF before any data,
   with exit code 1 on EOF later,
   and with exit code 2 on other errors.
 */
void process() {

  // have data.  
  int len;
  char *parse_table_name = recv_string(&len);
  if (len == -1) {
    // EOF before start of first string, okay
    exit(0);
  }
  if (len < 0) {
    exit(1-len);
  }
  DEBUG("parse table is %s\n", parse_table_name);

  char *input = recv_string(&len);
  if (len == -1) {
    exit(1);
  }
  if (len < 0) {
    exit(1-len);
  }

  char *start_symbol = recv_string(&len);
  if (len == -1) {
    exit(1);
  }
  if (len < 0) {
    exit(1-len);
  }
  DEBUG("start symbol is %s\n", parse_table_name);

  char *input_file_name = recv_string(&len);
  if (len == -1) {
    exit(1);
  }
  if (len < 0) {
    exit(1-len);
  }
  DEBUG("input file name is %s\n", parse_table_name);

  int aterm_size;
  char* aterm = parse(parse_table_name, input, start_symbol, input_file_name, &aterm_size);

  if (aterm_size < 0) {
    exit(2);
  }

  free(parse_table_name);
  free(input);
  free(start_symbol);
  free(input_file_name);

  unsigned int size = aterm_size;

  DEBUG("Got result of %d bytes\n", size);

  unsigned char byte0 = size % 256;
  size /= 256;
  unsigned char byte1 = size % 256;
  size /= 256;
  unsigned char byte2 = size % 256;
  size /= 256;
  unsigned char byte3 = size;
  putc(byte3, stdout);
  DEBUG("Wrote byte %u\n", byte3);
  putc(byte2, stdout);
  DEBUG("Wrote byte %u\n", byte2);
  putc(byte1, stdout);
  DEBUG("Wrote byte %u\n", byte1);
  putc(byte0, stdout);
  DEBUG("Wrote byte %u\n", byte0);
  ssize_t written = fwrite(aterm, 1, aterm_size, stdout);
  DEBUG("Wrote %zd bytes of aterm\n", written);
  if (written != aterm_size) {
    exit(2);
  }
  fflush(stdout);
  return;
}

int main(void) {
  init();
  DEBUG("Initialized sglr, waiting for input\n");
  while (1) {
    process();
  }
  return 0;
}
