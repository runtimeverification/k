load kernelc
kmod KERNELC-RACE-DETECTION is  including  KERNELC
 rule < k => race > * N:Nat = _ ...</ k => race > 
      < k => race > * N = _ ...</ k => race > [structural]

 rule < k => race > * N = _ ...</ k => race > 
       < k => race > * N ...</ k => race > [structural]

 rule < T => raceDetected >... <race> K:K </race> ...</ T => raceDetected > [structural]


  configuration
  <T?> 
     <threads> <thread*> 
       <k?> .K </k?>  <race?> .K </race?> 
       <env> .Map </env>
       <fstack> .List </fstack>
        <id> 0 </id> 
     </thread*> </threads>
     <locks> .Map </locks> 
     <cthreads> .Set </cthreads>       @latex("\\kBR")    
     <funs> .Map </funs>              
     <in> .List </in> 
     <out> "" </out> 
     <mem> .Map </mem> 
     <ptr> .Map </ptr> 
     <next> 1 </next> 
  </T?> 
  <result?> "" </result?>

  syntax CellLabel ::= raceDetected

endkm
