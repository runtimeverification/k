
module BASIC-RUN 
  configuration <T> <k> .K </k> </T>
  op run : KLabel -> Bag
  macro run(KL:KLabel) = <T>... <k>KL(.List{K})</k> ...</T>
end module
