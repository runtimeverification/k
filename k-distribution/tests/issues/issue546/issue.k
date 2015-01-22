// Copyright (c) 2012-2015 K Team. All Rights Reserved.
module ISSUE
  configuration <T> <a multiplicity="*"> <k> $PGM:K </k> </a> </T>
  rule <T> <a> <k> 1 </k> </a>
        => (<a> <k> 2 </k> </a>  <br/>  <a> <k> 3 </k> </a>)
       </T>
endmodule

