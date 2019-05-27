// Copyright (c) 2019 K Team. All Rights Reserved.

module H-SPEC
  imports INI-SPEC-GEN

    // h
    rule <k> bar(X) => end </k>
         <fooC> Y:Int </fooC>
         <alt> left </alt>
      requires true

    // h-1
    rule <k> bar(X) => end </k>
         <fooC> Y:Int </fooC>
         <alt> left </alt>
      requires Y <=Int 3
    [trusted]

    // h-2
    rule <k> bar(X) => end </k>
         <fooC> Y:Int </fooC>
         <alt> left </alt>
      requires Y >Int 3
    [trusted]


endmodule
