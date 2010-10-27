#include <stdio.h>

long zz() { return 0x00000000L; }
long zs() { return 0x0000ffffL; }
long zu() { return 0x00007fffL; }
long sz() { return 0xffff0000L; }
long ss() { return 0xffffffffL; }
long su() { return 0xffff7fffL; }
long uz() { return 0x7fff0000L; }
long us() { return 0x7fffffffL; }
long uu() { return 0x7fff7fffL; }

long long zzzz() { return 0x0000000000000000LL; }
long long zzzs() { return 0x000000000000ffffLL; }
long long zzzu() { return 0x0000000000007fffLL; }
long long zzsz() { return 0x00000000ffff0000LL; }
long long zzss() { return 0x00000000ffffffffLL; }
long long zzsu() { return 0x00000000ffff7fffLL; }
long long zzuz() { return 0x000000007fff0000LL; }
long long zzus() { return 0x000000007fffffffLL; }
long long zzuu() { return 0x000000007fff7fffLL; }
long long zszz() { return 0x0000ffff00000000LL; }
long long zszs() { return 0x0000ffff0000ffffLL; }
long long zszu() { return 0x0000ffff00007fffLL; }
long long zssz() { return 0x0000ffffffff0000LL; }
long long zsss() { return 0x0000ffffffffffffLL; }
long long zssu() { return 0x0000ffffffff7fffLL; }
long long zsuz() { return 0x0000ffff7fff0000LL; }
long long zsus() { return 0x0000ffff7fffffffLL; }
long long zsuu() { return 0x0000ffff7fff7fffLL; }
long long zuzz() { return 0x00007fff00000000LL; }
long long zuzs() { return 0x00007fff0000ffffLL; }
long long zuzu() { return 0x00007fff00007fffLL; }
long long zusz() { return 0x00007fffffff0000LL; }
long long zuss() { return 0x00007fffffffffffLL; }
long long zusu() { return 0x00007fffffff7fffLL; }
long long zuuz() { return 0x00007fff7fff0000LL; }
long long zuus() { return 0x00007fff7fffffffLL; }
long long zuuu() { return 0x00007fff7fff7fffLL; }
long long szzz() { return 0xffff000000000000LL; }
long long szzs() { return 0xffff00000000ffffLL; }
long long szzu() { return 0xffff000000007fffLL; }
long long szsz() { return 0xffff0000ffff0000LL; }
long long szss() { return 0xffff0000ffffffffLL; }
long long szsu() { return 0xffff0000ffff7fffLL; }
long long szuz() { return 0xffff00007fff0000LL; }
long long szus() { return 0xffff00007fffffffLL; }
long long szuu() { return 0xffff00007fff7fffLL; }
long long sszz() { return 0xffffffff00000000LL; }
long long sszs() { return 0xffffffff0000ffffLL; }
long long sszu() { return 0xffffffff00007fffLL; }
long long sssz() { return 0xffffffffffff0000LL; }
long long ssss() { return 0xffffffffffffffffLL; }
long long sssu() { return 0xffffffffffff7fffLL; }
long long ssuz() { return 0xffffffff7fff0000LL; }
long long ssus() { return 0xffffffff7fffffffLL; }
long long ssuu() { return 0xffffffff7fff7fffLL; }
long long suzz() { return 0xffff7fff00000000LL; }
long long suzs() { return 0xffff7fff0000ffffLL; }
long long suzu() { return 0xffff7fff00007fffLL; }
long long susz() { return 0xffff7fffffff0000LL; }
long long suss() { return 0xffff7fffffffffffLL; }
long long susu() { return 0xffff7fffffff7fffLL; }
long long suuz() { return 0xffff7fff7fff0000LL; }
long long suus() { return 0xffff7fff7fffffffLL; }
long long suuu() { return 0xffff7fff7fff7fffLL; }
long long uzzz() { return 0x7fff000000000000LL; }
long long uzzs() { return 0x7fff00000000ffffLL; }
long long uzzu() { return 0x7fff000000007fffLL; }
long long uzsz() { return 0x7fff0000ffff0000LL; }
long long uzss() { return 0x7fff0000ffffffffLL; }
long long uzsu() { return 0x7fff0000ffff7fffLL; }
long long uzuz() { return 0x7fff00007fff0000LL; }
long long uzus() { return 0x7fff00007fffffffLL; }
long long uzuu() { return 0x7fff00007fff7fffLL; }
long long uszz() { return 0x7fffffff00000000LL; }
long long uszs() { return 0x7fffffff0000ffffLL; }
long long uszu() { return 0x7fffffff00007fffLL; }
long long ussz() { return 0x7fffffffffff0000LL; }
long long usss() { return 0x7fffffffffffffffLL; }
long long ussu() { return 0x7fffffffffff7fffLL; }
long long usuz() { return 0x7fffffff7fff0000LL; }
long long usus() { return 0x7fffffff7fffffffLL; }
long long usuu() { return 0x7fffffff7fff7fffLL; }
long long uuzz() { return 0x7fff7fff00000000LL; }
long long uuzs() { return 0x7fff7fff0000ffffLL; }
long long uuzu() { return 0x7fff7fff00007fffLL; }
long long uusz() { return 0x7fff7fffffff0000LL; }
long long uuss() { return 0x7fff7fffffffffffLL; }
long long uusu() { return 0x7fff7fffffff7fffLL; }
long long uuuz() { return 0x7fff7fff7fff0000LL; }
long long uuus() { return 0x7fff7fff7fffffffLL; }
long long uuuu() { return 0x7fff7fff7fff7fffLL; }

long long bit00() { return 0x0000000000000001LL; }
long long bit01() { return 0x0000000000000002LL; }
long long bit02() { return 0x0000000000000004LL; }
long long bit03() { return 0x0000000000000008LL; }
long long bit04() { return 0x0000000000000010LL; }
long long bit05() { return 0x0000000000000020LL; }
long long bit06() { return 0x0000000000000040LL; }
long long bit07() { return 0x0000000000000080LL; }
long long bit08() { return 0x0000000000000100LL; }
long long bit09() { return 0x0000000000000200LL; }
long long bit10() { return 0x0000000000000400LL; }
long long bit11() { return 0x0000000000000800LL; }
long long bit12() { return 0x0000000000001000LL; }
long long bit13() { return 0x0000000000002000LL; }
long long bit14() { return 0x0000000000004000LL; }
long long bit15() { return 0x0000000000008000LL; }
long long bit16() { return 0x0000000000010000LL; }
long long bit17() { return 0x0000000000020000LL; }
long long bit18() { return 0x0000000000040000LL; }
long long bit19() { return 0x0000000000080000LL; }
long long bit20() { return 0x0000000000100000LL; }
long long bit21() { return 0x0000000000200000LL; }
long long bit22() { return 0x0000000000400000LL; }
long long bit23() { return 0x0000000000800000LL; }
long long bit24() { return 0x0000000001000000LL; }
long long bit25() { return 0x0000000002000000LL; }
long long bit26() { return 0x0000000004000000LL; }
long long bit27() { return 0x0000000008000000LL; }
long long bit28() { return 0x0000000010000000LL; }
long long bit29() { return 0x0000000020000000LL; }
long long bit30() { return 0x0000000040000000LL; }
long long bit31() { return 0x0000000080000000LL; }
long long bit32() { return 0x0000000100000000LL; }
long long bit33() { return 0x0000000200000000LL; }
long long bit34() { return 0x0000000400000000LL; }
long long bit35() { return 0x0000000800000000LL; }
long long bit36() { return 0x0000001000000000LL; }
long long bit37() { return 0x0000002000000000LL; }
long long bit38() { return 0x0000004000000000LL; }
long long bit39() { return 0x0000008000000000LL; }
long long bit40() { return 0x0000010000000000LL; }
long long bit41() { return 0x0000020000000000LL; }
long long bit42() { return 0x0000040000000000LL; }
long long bit43() { return 0x0000080000000000LL; }
long long bit44() { return 0x0000100000000000LL; }
long long bit45() { return 0x0000200000000000LL; }
long long bit46() { return 0x0000400000000000LL; }
long long bit47() { return 0x0000800000000000LL; }
long long bit48() { return 0x0001000000000000LL; }
long long bit49() { return 0x0002000000000000LL; }
long long bit50() { return 0x0004000000000000LL; }
long long bit51() { return 0x0008000000000000LL; }
long long bit52() { return 0x0010000000000000LL; }
long long bit53() { return 0x0020000000000000LL; }
long long bit54() { return 0x0040000000000000LL; }
long long bit55() { return 0x0080000000000000LL; }
long long bit56() { return 0x0100000000000000LL; }
long long bit57() { return 0x0200000000000000LL; }
long long bit58() { return 0x0400000000000000LL; }
long long bit59() { return 0x0800000000000000LL; }
long long bit60() { return 0x1000000000000000LL; }
long long bit61() { return 0x2000000000000000LL; }
long long bit62() { return 0x4000000000000000LL; }
long long bit63() { return 0x8000000000000000LL; }


int main(int argc, const char *argv[]) {
  printf("%08x\n", zz());
  printf("%08x\n", zs());
  printf("%08x\n", zu());
  printf("%08x\n", sz());
  printf("%08x\n", ss());
  printf("%08x\n", su());
  printf("%08x\n", uz());
  printf("%08x\n", us());
  printf("%08x\n", uu());
  
  printf("%016llx\n", zzzz());
  printf("%016llx\n", zzzs());
  printf("%016llx\n", zzzu());
  printf("%016llx\n", zzsz());
  printf("%016llx\n", zzss());
  printf("%016llx\n", zzsu());
  printf("%016llx\n", zzuz());
  printf("%016llx\n", zzus());
  printf("%016llx\n", zzuu());
  printf("%016llx\n", zszz());
  printf("%016llx\n", zszs());
  printf("%016llx\n", zszu());
  printf("%016llx\n", zssz());
  printf("%016llx\n", zsss());
  printf("%016llx\n", zssu());
  printf("%016llx\n", zsuz());
  printf("%016llx\n", zsus());
  printf("%016llx\n", zsuu());
  printf("%016llx\n", zuzz());
  printf("%016llx\n", zuzs());
  printf("%016llx\n", zuzu());
  printf("%016llx\n", zusz());
  printf("%016llx\n", zuss());
  printf("%016llx\n", zusu());
  printf("%016llx\n", zuuz());
  printf("%016llx\n", zuus());
  printf("%016llx\n", zuuu());
  printf("%016llx\n", szzz());
  printf("%016llx\n", szzs());
  printf("%016llx\n", szzu());
  printf("%016llx\n", szsz());
  printf("%016llx\n", szss());
  printf("%016llx\n", szsu());
  printf("%016llx\n", szuz());
  printf("%016llx\n", szus());
  printf("%016llx\n", szuu());
  printf("%016llx\n", sszz());
  printf("%016llx\n", sszs());
  printf("%016llx\n", sszu());
  printf("%016llx\n", sssz());
  printf("%016llx\n", ssss());
  printf("%016llx\n", sssu());
  printf("%016llx\n", ssuz());
  printf("%016llx\n", ssus());
  printf("%016llx\n", ssuu());
  printf("%016llx\n", suzz());
  printf("%016llx\n", suzs());
  printf("%016llx\n", suzu());
  printf("%016llx\n", susz());
  printf("%016llx\n", suss());
  printf("%016llx\n", susu());
  printf("%016llx\n", suuz());
  printf("%016llx\n", suus());
  printf("%016llx\n", suuu());
  printf("%016llx\n", uzzz());
  printf("%016llx\n", uzzs());
  printf("%016llx\n", uzzu());
  printf("%016llx\n", uzsz());
  printf("%016llx\n", uzss());
  printf("%016llx\n", uzsu());
  printf("%016llx\n", uzuz());
  printf("%016llx\n", uzus());
  printf("%016llx\n", uzuu());
  printf("%016llx\n", uszz());
  printf("%016llx\n", uszs());
  printf("%016llx\n", uszu());
  printf("%016llx\n", ussz());
  printf("%016llx\n", usss());
  printf("%016llx\n", ussu());
  printf("%016llx\n", usuz());
  printf("%016llx\n", usus());
  printf("%016llx\n", usuu());
  printf("%016llx\n", uuzz());
  printf("%016llx\n", uuzs());
  printf("%016llx\n", uuzu());
  printf("%016llx\n", uusz());
  printf("%016llx\n", uuss());
  printf("%016llx\n", uusu());
  printf("%016llx\n", uuuz());
  printf("%016llx\n", uuus());
  printf("%016llx\n", uuuu());

  printf("%016llx\n", bit00());
  printf("%016llx\n", bit01());
  printf("%016llx\n", bit02());
  printf("%016llx\n", bit03());
  printf("%016llx\n", bit04());
  printf("%016llx\n", bit05());
  printf("%016llx\n", bit06());
  printf("%016llx\n", bit07());
  printf("%016llx\n", bit08());
  printf("%016llx\n", bit09());
  printf("%016llx\n", bit10());
  printf("%016llx\n", bit11());
  printf("%016llx\n", bit12());
  printf("%016llx\n", bit13());
  printf("%016llx\n", bit14());
  printf("%016llx\n", bit15());
  printf("%016llx\n", bit16());
  printf("%016llx\n", bit17());
  printf("%016llx\n", bit18());
  printf("%016llx\n", bit19());
  printf("%016llx\n", bit20());
  printf("%016llx\n", bit21());
  printf("%016llx\n", bit22());
  printf("%016llx\n", bit23());
  printf("%016llx\n", bit24());
  printf("%016llx\n", bit25());
  printf("%016llx\n", bit26());
  printf("%016llx\n", bit27());
  printf("%016llx\n", bit28());
  printf("%016llx\n", bit29());
  printf("%016llx\n", bit30());
  printf("%016llx\n", bit31());
  printf("%016llx\n", bit32());
  printf("%016llx\n", bit33());
  printf("%016llx\n", bit34());
  printf("%016llx\n", bit35());
  printf("%016llx\n", bit36());
  printf("%016llx\n", bit37());
  printf("%016llx\n", bit38());
  printf("%016llx\n", bit39());
  printf("%016llx\n", bit40());
  printf("%016llx\n", bit41());
  printf("%016llx\n", bit42());
  printf("%016llx\n", bit43());
  printf("%016llx\n", bit44());
  printf("%016llx\n", bit45());
  printf("%016llx\n", bit46());
  printf("%016llx\n", bit47());
  printf("%016llx\n", bit48());
  printf("%016llx\n", bit49());
  printf("%016llx\n", bit50());
  printf("%016llx\n", bit51());
  printf("%016llx\n", bit52());
  printf("%016llx\n", bit53());
  printf("%016llx\n", bit54());
  printf("%016llx\n", bit55());
  printf("%016llx\n", bit56());
  printf("%016llx\n", bit57());
  printf("%016llx\n", bit58());
  printf("%016llx\n", bit59());
  printf("%016llx\n", bit60());
  printf("%016llx\n", bit61());
  printf("%016llx\n", bit62());
  printf("%016llx\n", bit63());

  return 0;
}
