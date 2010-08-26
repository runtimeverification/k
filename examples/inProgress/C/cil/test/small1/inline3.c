//MSVC considers _inline a keyword, but gcc doesn't.

//From linux-2.6.17.1/fs/jfs/jfs_incore.h:
struct {
  char _unused[16]; /* 16: */
  int _dxd[4];     /* 16: */
  char _inline[128];    /* 128: inline symlink */
  /* _inline_ea may overlay the last part of
   * file._xtroot if maxentry = XTROOTINITSLOT
   */
  char _inline_ea[128]; /* 128: inline extended attr */
} link;
