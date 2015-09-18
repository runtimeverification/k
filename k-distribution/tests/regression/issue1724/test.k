require "domains.k"

module TEST
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

