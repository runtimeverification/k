module FOO
     imports DOMAINS

     configuration
         <k> $PGM:Val </k>

     syntax Val ::= "foo" | "bar"
     rule <k> foo => bar ... </k>
     rule <k> bar => 0   ... </k>
 endmodule
