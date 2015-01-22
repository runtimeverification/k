// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module ISSUE

  syntax KItem ::= "read"

  configuration <T>
          <k> $PGM:K </k>
          <in stream="stdin"> $IN:List </in>
        </T>

  rule <k> read => I ...</k>
       <in> ListItem(I) => . ...</in>

endmodule