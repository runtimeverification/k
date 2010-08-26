

/* A special purpose main */
#include "main.h"
#include "hash.h"
#include "alloc.h"
#include "pccio.h"
#include "huffman.h"

/* Some globals that PCC needs */
int error_level, anerror;
void myexit(int n) {
  exit(n);
}
#ifdef _MSVC
#define random rand
#else
/* extern int random(void); -- Weimer: not needed! */
#endif
int __mmId;
int debugMM;
int debug = 0;  // Make this 1 to debug the compressor


/* Callback for writing to the compressed file */
int compressfid;
#define BUFFSIZE 1024
U8  outbuff[BUFFSIZE];
int outPoint = 0;
int written = 0;
static int flushOut(void) {
  int many;
  if(outPoint <= 0) return 0;
  many = write(compressfid, outbuff, outPoint);
  if(many != outPoint) {
    ERROR0(-1, "Error writing to the compressed file");
  }
  written += outPoint;
  outPoint = 0;
  return 0;
}
static int writeByte(U8 b) {
  outbuff[outPoint ++] = b;
  if(outPoint == BUFFSIZE) {
    flushOut();
  }
  return 0;
}

#define TIMES 10
int main(int argc, char **argv) {
  PHASH freq = NewHash();
  int freqfid, codefid;
  int nrSource, delta;
  double clk;
  int count = 0;

  INDATA srcFile, compFile;
  
  /* Must be passed the name of a file to compress */
  if(argc < 2) {
    printf("Must give a file to compress\n");
    exit(1);
  }
  TIMESTART(clk);

  initLFIOFile(&srcFile, argv[1]);
  
  /* Read the file, 2 bytes at a time and create the frequency table */
  nrSource = 0;
  while(canFetch(&srcFile, 2)) {
    U16 wrd = fetchWordLE(&srcFile);
    nrSource += 2;
    bumpFrequency(freq, wrd);
  }
  finishIOFile(&srcFile);
  printf("Read %d bytes\n", nrSource);
  /* Open the code and frequency files */
  freqfid = CREAT("huffman.freq");
  codefid = CREAT("huffman.code");
  compressfid = CREAT("huffman.compressed");
  if(freqfid < 0 || codefid < 0 || compressfid < 0) {
    ERROR0(1, "Cannot create frequency and code files\n");
  }
  createCompressTables(freq, freqfid, codefid);
  close(freqfid); close(codefid);
  FreeHash(freq);
  
  /* Now read again and compress */
  initCompressor("huffman.code");
  initLFIOFile(&srcFile, argv[1]);
  outPoint = 0; written = 0;
  startCompress(&writeByte);
  /* Read the file, 2 bytes at a time and compress */
  while(canFetch(&srcFile, 2)) {
    U16 wrd = fetchWordLE(&srcFile);
    writeCompressedSymbol(wrd);
  }
  endCompress();
  flushOut();
  close(compressfid);
  finishIOFile(&srcFile);

  /* Now decompress and compare */
  for(count=0;count<30;count++) {
    initLFIOFile(&compFile, "huffman.compressed");
    initLFIOFile(&srcFile, argv[1]);
    startDecompress();
    delta = nrSource;
    while(delta > 0) {
      int comp = fetchCompressedSymbol(&compFile);
      int src  = fetchWordLE(&srcFile);
      if(src != comp) {
        ERROR3(-1, "Src(%04x) != Comp(%04x) (at offset %d)\n",
               src, comp, nrSource - delta);
      }
      delta -= 2;
    }
    endDecompress(&compFile);
    finishIOFile(&srcFile); finishIOFile(&compFile);
  }
  finalizeCompressor();


  TIMESTOP(clk);
  
  // sm: according to my man pages, the 'l' flag doesn't apply
  // to the 'f' format, which is always a double argument
  printf("Source %d bytes. Compressed %d bytes. Ratio: %5.2f\n",
         nrSource, written, (double)nrSource / (double)written);
  printf("Run hufftest in %8.3fms\n", clk / 1000.0);
  exit (0);
  return 0;
}


