module TEST
  imports LIST
  imports STRING

  configuration <T color="yellow">
                  <k color="green"> $PGM:K </k>
                  <input color="magenta" stream="stdin"> .List </input>
                  <output color="Orchid" stream="stdout"> .List </output>
                </T>

endmodule
