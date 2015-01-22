// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module EXTENDED-FLOAT
  syntax Float ::= Token{[\-]? [0][xX] [0-9a-fA-F] [\.] [0-9a-fA-F]* [pP] [\-\+]? [0-9]+}

                                 >   "--Float64" Float              [function, hook(#FLOAT:_-Float64)]
                 > Float "^Float64" Float        [function, left, latex({#1}^{#2}), hook(#FLOAT:_^Float64_)]
                                 > left:
                   Float "*Float64" Float        [function, left, latex({#1}\mathrel{\ast_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_*Float64_)]
                 | Float "/Float64" Float        [function, left, latex({#1}\mathrel{\div_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_/Float64_)]
                 | Float "%Float64" Float        [function, left, latex({#1}\mathrel{\%_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_%Float64_)]
                 > left:
                   Float "+Float64" Float        [function, left, latex({#1}\mathrel{+_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_+Float64_)]
                 | Float "-Float64" Float        [function, left, latex({#1}\mathrel{-_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_-Float64_)]

endmodule
