load ../../../k-prelude
kmod BASIC-RUN is  including K
  configuration <T> <k> .K </k> </T>
  op run : KLabel -> Bag
  macro run(KL:KLabel) = <T_> <k>KL(.List{K})</k> <_/T>
endkm
