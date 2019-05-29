module TEST

   imports INT

   configuration <x>  <k> $PGM:K </k> </x>

   syntax KItem ::= freshIntx() [function]

   rule freshIntx() => !I:Int

   rule 5 => freshIntx()

endmodule
