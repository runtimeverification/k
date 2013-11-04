require "builtins/list.k"

module TEST
  imports LIST

  syntax MyList ::= init(Int)
                  | initLeft(Int)   [function]
                  | initRight(Int)  [function]
  rule init(N) => initLeft(N), initRight(N)
  rule initLeft(N) => initLeft(N -Int 1), MyListItem(N)
  when N >=Int 0
  rule initLeft(N) => .MyList
  when N <Int 0
  rule initRight(N) => MyListItem(N), initRight(N -Int 1)
  when N >=Int 0
  rule initRight(N) => .MyList
  when N <Int 0
endmodule

