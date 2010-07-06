load ../../../../k-prelude
load ../../sort

load programs

kmod RUN is including SORT-PROGRAMS
  op run : List -> Bag
  macro run(L:List) = <sortme> L </sortme>
endkm
