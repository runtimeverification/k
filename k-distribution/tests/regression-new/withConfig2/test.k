// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST

   imports INT

   configuration <x>  <k> $PGM:K </k> </x>

   syntax KItem ::= freshIntx() [function]

   rule freshIntx() => !_I:Int

   rule 5 => freshIntx()

   rule 6 => test()

   syntax Int ::= test() [function]

   rule [[ test() => 7 ]]
        <k> 6 ...</k>

endmodule
