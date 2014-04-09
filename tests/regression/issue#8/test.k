require "builtins/list.k"

module TEST
imports LIST

configuration <out> MyListItem(5), MyListItem(6) </out>

rule <out> .MyList, (MyListItem(5), (L:MyList, MyListItem(6))) => . </out>
rule <out> .MyList, ((MyListItem(5), L:MyList), MyListItem(6)) => . </out>

endmodule

