// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
  imports INT

  configuration <k> $PGM:K </k>

  configuration <bar> 1 </bar>

  rule <k> _:Int => initBarCell ...</k>
endmodule
