module TEST
   imports INT
   imports BOOL
   imports LIST

   syntax List ::= Int ":" List [macro]
   rule I : L => ListItem(I) L

   rule (5 => 6) : _

endmodule
