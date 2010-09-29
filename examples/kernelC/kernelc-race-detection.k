kmod KERNELC-RACE-DETECTION is  including  BASIC-KERNELC-SEMANTICS
  syntax CellLabel ::= raceDetected
  configuration <T> <threads> <thread*> < k ? > .K </ k ? > < race ? > .K </ race ? > <env> .Map </env> <id> 0 </id> </thread*> 
                    </threads>  <cthreads> .Set </cthreads>
                    <funs> .Map </funs> <in> .List </in> <out> "" </out> 
                   <mem> .Map </mem> <ptr> .Map </ptr> 
                   <locks> .Map </locks> <next> initialLoc </next> </T> 
                <result> "" </result>
--- rule < T => race >... < k => race > * N:Nat = E:Exp ...</ k => race > < k => race > * N:Nat = E':Exp ...</ k => race > ...</ T => race > [structural]
---  rule < T => race >... < k => race > * N:Nat = E:Exp ...</ k => race > < k => race > * N:Nat ...</ k => race > ...</ T => race > [structural]
 rule < k => race > * N:Nat = E:Exp ...</ k => race > 
      < k => race > * N:Nat = E':Exp ...</ k => race > [structural]
 rule < k => race > * N:Nat = E:Exp ...</ k => race > 
       < k => race > * N:Nat ...</ k => race > [structural]

 rule < T => raceDetected >... <race> K:K </race> ...</ T => raceDetected > [structural]
endkm
