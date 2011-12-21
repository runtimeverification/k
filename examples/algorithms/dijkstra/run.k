
load nat-inf
load dijkstra

load programs

kmod RUN is including DIJKSTRA-PROGRAMS
  op run : Set #Id -> Bag
  macro run(Graph:Set,x:#Id) = <graph> Graph </graph> 
                              <shortest> x |-> 0 </shortest>

  rule <graph>... x -_-> _ ...</graph>  
       <shortest> M:Map (. => x |-> infty) </shortest> 
    when notBool(x in keys(M))   [structural]
  rule <graph>... _ -_-> x ...</graph>  
       <shortest> M:Map (. => x |-> infty) </shortest> 
    when notBool(x in keys(M))   [structural]
endkm
