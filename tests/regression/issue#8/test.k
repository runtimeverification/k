// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/list.k"

module TEST
  imports LIST

configuration <out> ListItem(5) ListItem(6) </out>

rule <out> .List (ListItem(5) (L:List ListItem(6))) => . </out>
rule <out> .List ((ListItem(5) L:List) ListItem(6)) => . </out>

endmodule

