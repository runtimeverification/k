module TEST
  imports DOMAINS

  configuration
    <k> $PGM:Stmt </k>
    <vals> .List </vals>
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
                | present(Int)
                | Stmt ";" Stmt [left]
  rule
    <k> get(Key) => . ...</k>
    <key> Key </key>
    <value> Value:Int </value>
    <vals> ... (.List => ListItem(Value)) </vals>

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

  rule
    <k> present(I) => . ... </k>
    <map> MAP </map>
    <vals> ... (.List => ListItem(<key> I </key> in_keys(MAP))) </vals>

  rule <k> S1; S2 => S1 ~> S2 ... </k>
endmodule
