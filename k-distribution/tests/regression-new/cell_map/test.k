module TEST
  imports DOMAINS

  configuration
    <k> $PGM:Stmt </k>
    <map>
      <entry multiplicity="*" type="Map">
        <key> .K </key>
        <value> .K </value>
      </entry>
    </map>

  syntax Stmt ::= get(Int)
                | insert(Int, Int)
                | remove(Int)
                | update(Int, Int)
                | Stmt ";" Stmt
  rule
    <k> get(Key) => Value ...</k>
    <key> Key </key>
    <value> Value:Int </value>
  rule
    <k> insert(Key, Value) => .K ...</k>
    <map>...
      .Bag => <entry> <key> Key </key> <value> Value </value> </entry>
    ...</map>
  rule
    <k> remove(Key) => .K ...</k>
    <map>...
      <entry> <key> Key </key> <value> _ </value> </entry> => .Bag
    ...</map>
  rule
    <k> update(Key, Value) => .K ...</k>
    <key> Key </key>
    <value> _ => Value </value>
  rule S1; S2 => S1 ~> S2
endmodule
