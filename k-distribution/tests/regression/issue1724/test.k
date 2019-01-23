// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "domains.k"

module TEST-SYNTAX
  imports INT-SYNTAX
endmodule

module TEST
  imports TEST-SYNTAX
  imports INT

  configuration
    <T>
      <threads multiplicity="?">
        <thread multiplicity="*">
          <k> $PGM:Int </k>
        </thread>
      </threads>
    </T>

  rule <threads> .Bag </threads> => .Bag
endmodule

