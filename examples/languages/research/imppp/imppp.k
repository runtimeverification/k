module IMPPP-SYNTAX
//@ \section{Syntax}

//@ \subsection{The old IMP constructs}
  syntax AExp ::= #Id | #Int
                | AExp "+" AExp                      [:prec(33) gather (E e) strict:]
                | AExp "/" AExp                      [:prec(31) gather (E e) superheat strict:]
  syntax BExp ::= #Bool
                | AExp "<=" AExp                     [:prec(37) seqstrict latex("{#1}\leq{#2}"):]
                | "not" BExp                         [:prec(53) strict:]
                | BExp "and" BExp                    [:prec(55) strict(1):]
  syntax Stmt ::= "skip"
                | #Id ":=" AExp                      [:prec(80) strict(2):]
                | Stmt ";" Stmt                      [:prec(100) gather(e E):]
                | "if" BExp "then" Stmt "else" Stmt  [:prec(85) strict(1):]
                | "while" BExp "do" Stmt             [:prec(85):]

//@ \subsection{The new IMP++ constructs}
  syntax AExp ::= "++" #Id                           [:prec(0):]
                | "read" "(" ")"

  syntax Stmt ::= "print" "(" PExp ")"               [:strict:]
                | "halt"
                | "spawn" Stmt                       [:prec(90):]
                | "{" "}"
                | "{" Stmt "}"                       [:gather(&):]
                | "var" Ids                          [:prec(70):]

//@ We prefer aliases for lists
  syntax Ids ::= List{#Id,","}
//@ \textit{PExp} useful for the \texttt{print} statement (either an expression or a string)
  syntax PExp ::= AExp | #String 
end module


module IMPPP imports IMPPP-SYNTAX
//@ \section{Semantics}

  syntax KResult ::= #Bool | #Int | #String

/*@ \subsection{Configuration}
The original configuration of IMP has been extended to include
all the various additional cells needed for IMP++.  */

  configuration
    <T color="yellow">
      <threads color="orange">
        <thread multiplicity="*" color="red">
          <k color="green">$PGM:K</k>
          <env color="LightSkyBlue">.Map</env>
        </thread>
     </threads>
     <br/>
     <store color="white">.Map</store>
     <nextLoc color="gray">0</nextLoc>
//     <in color="magenta"> $IN:List </in>
//     <out color="Orchid"> .List </out>
     <in color="magenta" stream="stdin"> $IN:List </in>
     <out color="Orchid" stream="stdout">.List</out>
    </T>

//@ \subsection{The old IMP constructs}

//@ \subsubsection{Variable lookup}
  rule <k> X:#Id => I ...</k>
       <env>... X |-> N:#Nat ...</env>
       <store>... N |-> I:#Int ...</store> [supercool transition]

//@ \subsubsection{Arithmetic constructs}
  rule I1:#Int + I2:#Int => I1 +Int I2
  rule I1 / I2 => I1 /Int I2 if I2 =/=Bool 0

//@ \subsubsection{Boolean constructs}
  rule I1 <= I2 => I1 <=Int I2
  rule not T:#Bool => notBool T
  rule true and B:BExp => B
  rule false and B => false

//@ \subsubsection{Skip}
  rule skip => .

//@ \subsubsection{Variable assignment}
  rule <k> X := I => . ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (_ => I) ...</store> [transition]

//@ \subsubsection{Sequential composition}
  rule S1:Stmt ; S2:Stmt => S1 ~> S2 [structural]

//@ \subsubsection{Conditional}
  rule if  true then S1 else _  => S1
  rule if false then _  else S2 => S2

//@ \subsubsection{While loop}
  rule <k> while B do S:Stmt => if B then S ; while B do S else {} ...</k>

//@ \subsection{The new IMP++ constructs}

//@ \subsubsection{Variable increment}
  rule <k> ++X => I +Int 1 ...</k>
       <env>... X |-> N ...</env>
       <store>... N |-> (I => I +Int 1) ...</store> [supercool transition]

//@ \subsubsection{Input}
  rule <k> read() => I ...</k>
       <in> ListItem(I) => . ...</in> [transition]

//@ \subsubsection{Output}
  rule <k> print(I) => . ...</k>
       <out>... . => ListItem(I) </out> [transition]
  rule <k> print(Str:#String) => . ...</k>
       <out>... . => ListItem(Str) </out> [transition]

//@ \subsubsection{Halt}
  rule <threads>... <k> halt ...</k> ...</threads> => .

//@ \subsubsection{Spawn thread}
  rule <k> spawn S => . ...</k>
       <env> Rho </env>
       (. => <thread>... <k> S </k> <env> Rho </env> ...</thread>)

//@ \subsubsection{Terminate thread}
  rule <thread>... <k> .K </k> ...</thread> => .

//@ \subsubsection{Blocks}
  rule {} => .
  rule <k> {S} => S ~> env(Rho) ...</k>
       <env> Rho:Map </env>

//@ \subsubsection{Variable declaration}
  rule var .Ids => .
  rule <k> var (X,Xl => Xl:Ids) ...</k>
       <env> Rho => Rho[N/X] </env>
       <store>... . => N |-> 0 ...</store>
       <nextLoc> N => sNat N </nextLoc>

//@ \subsubsection{Auxiliary operations}
//@ Environment recovery
  syntax K ::= env Map
  rule (env(_) => .) ~> env(_) [structural]
  rule <k> env(Rho) => . ...</k> <env> _ => Rho </env> [structural]
end module
