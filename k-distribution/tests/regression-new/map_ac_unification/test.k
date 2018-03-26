module TEST
  imports DOMAINS

  configuration
    <k> $PGM:Pgm </k>
    <map> .Map </map>

  syntax Pgm ::= "init0"
               | "op0"
               | Pgm ";" Pgm

  rule
    <k> init0 => .K ...</k>
    <map>
      _:Map
    =>
      ?I0:Int |-> ?J0:Int
      ?I1:Int |-> ?J1:Int
      0 |-> ?J2:Int
      ?M:Map
    </map>
  rule
    <k> op0 => .K ...</k>
    <map>...
      I0:Int |-> J0:Int
      I1:Int |-> J1:Int
      I2:Int |-> J2:Int
      0 |-> J3:Int
    ...</map>
    [transition]

  rule P1:Pgm ; P2:Pgm => P1 ~> P2
endmodule
