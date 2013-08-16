require "builtins/list.k"

module TEST
  imports LIST 
  configuration <out> MyListItem(1) MyListItem(3) MyListItem(2) </out>
  rule <out> MyListItem(1) (MyListItem(3) => .MyList) ...</out>
endmodule
