
module BASIC-RUN 
  configuration <T> <k> .K </k> </T>
  op run : KLabel -> Bag
  macro run(KL:KLabel) = <T_> <k>KL(.List{K})</k> <_/T>
end module
