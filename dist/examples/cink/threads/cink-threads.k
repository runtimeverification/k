require "../basic/cink-basic-syntax.k"
require "../basic/cink-basic-semantics.k"

module CINK-THREADS-SYNTAX

  syntax Stmt ::= "std::thread" Id "(" Exps ")" ";"

endmodule

module CINK-THREADS-SEMANTICS
  imports CINK-BASIC-SYNTAX
  imports CINK-THREADS-SYNTAX

  syntax K ::= "noName"

  configuration   <threads color="pink">
                    <thread multiplicity="*" color="purple"> 
                      <name color="yellow"> noName </name>
                      <k color="green"> .K </k>
                      <env color="LightSkyBlue"> .Map </env>
                    </thread>
                  </threads>
  

  /*@
    \subsection{Threads.}
    For now, \Cink includes a minimal support for threads, namely the creation 
    of a thread and the ending of a thread. The statement for creating a thread
    specifies the name of the thread \textit{T}, the name of a function
    \textit{F}, and the arguments \textit{El} of the function.
    The rule giving semantics to this statement, creates a new cell 
    \texttt{thread}, where the computation from the cell \texttt{k} of the new
    thread is the function call expression given as arguments, and the
    environment of the new thread is current environment of the current
    thread.
  */

  rule <thread>...
         <k> std::thread T:Id(F:Id, El:Exps); => . ...</k>
         <env> Env:Map </env>
       ...</thread>
       (. => 
        <thread>... 
          <name> T </name>  
          <k> F(El); </k>
          <env> Env </env>  
        ...</thread>
       )
       [thread]

  /*@
    A thread is finished (and deleted) when the content of its \texttt{k}
    cell is empty:
  */
  rule <thread>... <k> .K </k>  ...</thread> => . [thread-end]

endmodule

