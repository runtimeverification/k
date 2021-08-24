module OUTFIT

  syntax Boolean  ::= True()
                    | False()
                    | outfitMatching(Outfit) [function]

  syntax Color    ::= Black()
                    | White()

  syntax Hat      ::= Hat(Color)
  syntax Shirt    ::= Shirt(Color)
  syntax Pants    ::= Pants(Color)
  syntax Shoes    ::= Shoes(Color)

  syntax Outfit   ::= Outfit(Hat, Shirt, Pants, Shoes)

  rule outfitMatching(Outfit(Hat(C), Shirt(C), Pants(C), Shoes(C))) => True()

endmodule
