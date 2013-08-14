require "builtins/list.k"

module TEST
imports LIST

configuration $PGM:K .MyList

rule .MyList (MyListItem(5) (L:MyList MyListItem(6))) => .

endmodule

