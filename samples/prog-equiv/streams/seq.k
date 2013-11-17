require "builtins/symbolic-k.k"


//@ \section{Syntax}

module STREAM-SYNTAX


  //@ Integer Expressions
  syntax IExp ::=  Int
                | "hd" "(" SExp ")" [strict, context(svalue)]

  //@ Stream Expressions
  syntax SExp ::= Id
                | "tl" "(" SExp ")" [strict, context(svalue), prefer]
                > Id "(" SExps ")" [strict(2), context(svalue)]
                > IExp ":" SExp [right]
                | "[]"
  syntax SExps ::= List{SExp,","} [strict, context(svalue)]

  //@ Expressions
  syntax Exp ::= IExp | SExp

  //@ Stream Specifications
  syntax SSpec ::= Id ":=" SExp ";"
                 | Id "(" Ids ")" ":=" SExp ";"
  syntax Ids ::= List{Id,","}
  syntax SSpecs ::= SSpec | SSpec SSpecs [right]

/*@ A program is a sequence of specification followed by an 
  expression to be evaluated. If the expression is a stream one, then
  the evaluation is a infinite process and therefore the debugger should
  be used for such cases.
*/
  syntax SPgm ::= SSpecs Exp 


/*@
  The following syntax is specific to the program equivalence.
*/



  syntax EqvPgm ::= "<k>" SExp "</k>"
                    "<sspecs>" SSpecs "</sspecs>"
                    "~" 
                    "<k>" SExp "</k>"
                    "<sspecs>" SSpecs "</sspecs>" ";"

  syntax Start ::= EqvPgm  


  /*@
    Extending with symbolic values:
   */

  syntax IExp ::= "#symIExp" "(" Id ")"  [onlyLabel, klabel(#symIExp)]

  syntax SExp ::= "#symSExp" "(" Id ")"  [onlyLabel, klabel(#symSExp)]

  syntax Int ::= "#symInt" "(" Id ")" [onlyLabel, klabel(#symInt)]

endmodule


/*!
\setlength{\parindent}{1em}
\title{PEQ (Program Equivalence)}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro}) and Vlad Rusu (Vlad.Rusu@inria.fr)}
\organization{"Alexandru Ioan Cuza" University of Iasi, INRIA Lille}
*/

//@ \section{Symbolic Maps}

module SYMBOLIC-DOMAIN
  imports STREAM-SYNTAX

/*@ Matching Logic (ML) implication\\
This implication is used to test satisfaction relation between the circular hypothesis and
the current confuguration. Therefore we assume that it is of the form
$\pattern{\pi}{\phi}\implies \pattern{\pi'}{\phi'}$, where $\pattern{\pi}{\phi}$ will play
the role of the current configuration, and $\pattern{\pi'}{\phi'}$ the role of the 
hypothesis. Further, we always assume that $\pattern{\pi'}{\phi'}$ is in abstract form,
i.e., of the form $(\exists X)$\pattern{\overline{\pi}'}{\phi'\land \sigma}$, 
where \emph{$\overline{\pi}$ is an abstraction of $\pi$ via $\sigma^\pi$} 
(i.e., $\sigma^\pi(\overline{\pi})=\pi$), and $\sigma^\pi$ in the pattern condition is viewed
as a conjunction formula $\bigwedge x = \sigma^\pi(x)$ (the equality is in the symbolic
domain.\\
Since the current pattern condition is always satisfiable, the implication is equivalent to
$\phi\land \bigwedge\sigma\implies \phi'$, where $\sigma$ is the substitution that satisfies
$\sigma(\pi')=\sigma(pi)$ (we assume that the abstractions are defined such that such a
substitution always exists).
 

/*@
  Try to compute the substitution between two programs.
  The definition of \texttt{getSubst} depends on  the syntax of the language.
  Any extension of the language implies the update of this definition.
*/

  syntax Substitution ::= "getSubst" "(" K "," K ")" [function]
            |  K "replBy" K [strict]  // a substitution pair
            |  Substitution ";;" Substitution [left]      // concatenation of substitutions
            |  "emptySubst"

  rule getSubst(K:K, K) => emptySubst

 

  rule getSubst(K1:K ~> K2:K, K1':K ~> K2':K)
       =>
       getSubst(K1, K1') ;; getSubst(K2, K2')
       when (K1 =/=K .K)
       andBool (K2 =/=K .K)
       andBool (K1' =/=K .K)
       andBool (K2' =/=K .K)


  rule getSubst(X:Id, SE:SExp) => (X replBy SE)

  rule getSubst(X:Id, IE:IExp) => (X replBy IE)
  
  rule getSubst(#symSExp(X:K), SE:SExp) => (#symSExp(X) replBy SE)

  rule getSubst(#symInt(X:K), IE:IExp) => (#symInt(X) replBy IE)

  rule getSubst(hd(SE:SExp), hd(SE':SExps)) => getSubst(SE, SE') 

  rule getSubst(tl(SE:SExp), tl(SE':SExps)) => getSubst(SE, SE') 

  rule getSubst(F:Id(SEs:SExps), F(SEs':SExps)) => getSubst(SEs, SEs')

  rule getSubst((IE:SExp : SE:SExp), (IE':IExp : SE':SExp))
       => getSubst(IE, IE') ;; getSubst(SE, SE')

  rule getSubst((SE:SExp, SEs:SExps), (SE':SExp, SEs':SExps))
       => getSubst(SE, SE') ;; getSubst(SEs, SEs')

  rule getSubst(.Exps, .Exps) => emptySubst

  // to be completed


/*@
  Check if a Substitution is indeed a substitution:
*/

  syntax K ::= "isSubst" "("  K ")"  [function]

  rule isSubst(emptySubst) => true

  rule isSubst(I:K replBy A:K) => true

  rule isSubst(M:K ;; (I:K replBy A:K)) => isSubst(M)


 //@ Two auxiliary rules

  rule S:Substitution ;; emptySubst => S [anywhere]

  rule emptySubst ;; S:Substitution => S [anywhere]




/*@
  The observational equivalence relation is defined by checking the equality of
  the observer variables in the two configurations (see how \texttt{eqObs} is 
  called.
*/

/*
  syntax Bool ::= "eqObs" "(" OutCellSort "," OutCellSort ")" [function]

  rule eqObs(<out> SE:SExp </out>,
             <out> SE </out>)
       =>
       true
*/

  //@ \section{Auxiliary Operations}

  //@ Substitution

  syntax SExp ::= SExp "[" SExps "/" Ids "]" [function]

  rule SE:SExp[(V:SExp, (V':SExp, Vs:SExps)) / (X:Id, (X':Id, Xs:Ids))] => (replace(X, V, SE))[(V', Vs) / (X', Xs)]

  rule SE:SExp[(V:SExp, .SExps) / (X:Id, .Ids)] => replace(X, V, SE)


  //@ Append

  syntax SExp ::= append(Int, SExp) [function]

  rule append(I:Int, []) => I : []
  rule append(I:Int, (J:Int : SE)) => J : append(I, SE)


  //@ Replace X:K by V:K in E:K

  syntax K ::= replace(K,K,K) [function]
  syntax KList ::= replaceList(K,K,KList) [function]
  syntax KList ::= replaceListList(KList,K,KList) [function]

  rule replace(X:K, V:K, X) => V
  rule replace(XL:KLabel(XKL:KList), V:K, EL:KLabel(EKL:KList))
        =>
       EL(replaceList(XL(XKL), V, EKL))  when XL =/=KLabel EL
  rule replace(XL:KLabel(XKL:KList), V:K, XL:KLabel(EKL:KList))
        =>
        XL(replaceListList(XKL, V, EKL))

  rule replaceList(X:K, V:K, .KList) => .KList
  rule replaceList(X:K, V:K, (E:K,, EKL:KList))
       =>
       replace(X, V, E),, replaceList(X, V, EKL)

  rule replaceListList(.KList, V:K, EKL:KList) => EKL
  rule replaceListList((X:K,, XKL:KList), V:K, (E:K,, EKL:KList))
       =>
       replace(X, V, E),, replaceListList(XKL, V, EKL)



//@ \section{Semantics}

module SEQ
  imports SYMBOLIC-DOMAIN


/*@
  A configuration is a multiset of goals. Each goal consists of an
  equivalence formula. The patterns are stored into a \texttt{config}
  cell and the condition in the \texttt{condition} cell.
  The cell \texttt{hypos} is for storing the hypotheses met during
  the proving process. It has a structure similar to that of goals, but
  where the names of cells are changed in order to forbid the rules firing
  for hypotheses, in this way the hypotheses are kept unchanged. 
  The cell \texttt{observers} stores the list of the observer variables.
*/

  configuration <T color="yellow"> 
                  <goals> 
                    <goal multiplicity="*">
                      <config multiplicity="*">
                        <k color="green"> $PGM:EqvPgm  </k>
                        <sspecs color="red"> .Map </sspecs>
                        <out> [] </out> 
                      </config>
                    </goal>
                  </goals>
                  <hypos>
                    <hypo multiplicity="*">
                      <patt1>
                        <hk1 color="green"> .K  </hk1>
                        <hsspecs1 color="red"> .Map </hsspecs11>
                        <hout1> [] </hout1> 
                      </patt1>
                      <patt2>
                        <hk2 color="green"> .K  </hk2>
                        <hsspec2 color="red"> .Map </hsspec2>
                        <hout2> [] </hout2> 
                      </patt2>
                    </hypo>
                  </hypos>
<debug> .K </debug>
                </T>

 //@ The right-hand side of a specification is stored as a $\lambda$-expression:
  syntax K ::= "lambda" "(" Ids ")" SExp

/*@ The result values are integers and stream expression for that at  least
  the head is evaluated to an integer:
*/
  syntax KResult ::= Int 

  rule isKResult(_:Int : _:SExp) => true

/*@
  We use a new syntactic construct that help us to store hypotheses. The basic
  idea is to add the hypotheses in a controlled way. For instance, we may add
  hypothesis only when on the top in the two k cells we have  statement with
  the same label (the label is a kind of "rendevous" synchronisarion). 
*/

  syntax K ::= "storeHypo" "(" K ")"   // for storing hypotheses

            |  "checkHypo" "(" K "," Map "," K "," Map "," HyposCellFragment ")"
               // for checking hypotheses one by one 

  syntax K ::= "break"  // to temporarily stop one of the two programs

//@ Contexts
  syntax K ::= svalue(K) [klabel(svalue)]
/*@
  We have to specify which arguments of the svalu context are strict:
*/

  context svalue(hd(HOLE => svalue(HOLE)))  // a head argument
  context svalue(tl(HOLE => svalue(HOLE)))  // a tail argument
  context svalue((HOLE => svalue(HOLE)) : _) // the constructor: 1st case
  context svalue((HOLE => svalue(HOLE)), _:SExps) // the constructor: 2nd case
  context svalue(_:SExp, (HOLE => svalue(HOLE)))  // expression list: 1st case
  context svalue((HOLE => svalue(HOLE)), .SExps)  // expression list: 2nd case

 //@ Computations:
  rule IE:IExp : SE':SExp => IE ~> SE'

 //@ The evaluation of the head:
  rule svalue(hd(I:Int : _) => I)

  rule hd(I:Int : _) => I

  //@ The evaluation of tail:
  rule svalue(tl(_:Int : SE:SExp) => SE)

  rule tl(_:Int : SE:SExp) => SE
  
  //@ When the head is completely evaluated is move in the cell out:
  rule <k> I:Int => . ...</k>
       <out> SE:SExp => append(I, SE) </out>

 //@ Stream specification without parameters:
  rule <k> svalue(F:Id => SE) ...</k>
       <sspecs>... F |-> lambda(.Ids) SE:SExp ...</sspecs>

  rule <k> F:Id => SE ...</k>
       <sspecs>... F |-> lambda(.Ids) SE:SExp ...</sspecs>
       [transition]

 //@ Stream specification with parameters:
  rule <k> svalue(F:Id(SEs:SExps) => SE[SEs / Xs]) ...</k>
       <sspecs>... F |-> lambda(Xs:Ids) SE:SExp ...</sspecs>

  rule <k> F:Id(SEs:SExps) => SE[SEs / Xs] ...</k>
       <sspecs>... F |-> lambda(Xs:Ids) SE:SExp ...</sspecs>
       [transition]


/*@
  The next rule implements the basic entailment relation. The current version
  is incomplete because we have to show it is sound on the tested (it is depending on
  hpw the observation relation is defined). 
  We have to elaborate the implementation of the basic
  entailment.
*/

  rule [obs-equality] :
       (<goal>
         <config>
           <k> K:K </k>
           <sspecs> _:Map </sspecs>
           <out> OUT:SSpec </out>
         </config>
         <config>
           <k> K </k>
           <sspecs> _:Map </sspecs>
           <out> OUT' </out>
         </config>
       </goal>
       =>
       .)
       when OUT ==K OUT'
//       [transition]



/*@
  The followings defines (special) cases when a current goal is a 
  consequence of the circular hypotheses.\\
  This relation must be more elaborated.
*/


/*@
  When two statemets with the same label are synchronized, there are two ways
  to continue:
  1) apply circularity deduction rule if there is an hypothesis that matches the current
     formula;
  2) store the current formula as a circular hypothesis when such an hypothesis does not
     exist.
  We use the auxiliary semantic statement checkHypo for deciding between the two cases.
  Note: the semantics of lbldStmt is similar to that of threads synchronization.
*/

  rule [stmt-sync] : 
       <goal>
         <config> 
           <k> SE1:SExp => checkHypo(SE1, SE2, Hypos) ...</k>
           <sspecs> SSp1:Map </sspecs>
           <out> OUT1:SExp </out>
         </config> 
         <config> 
           <k> SE2:SExp => break ...</k>
           <sspecs> SSp2:Map </sspecs>
           <out> OUT2:SExp </out>
         </config>
       </goal>
       <hypos>
         Hypos:Bag
       </hypos>
//      [transition]

  /*@ The case when the set of hypotheses is empty and 
       the configurations are observational equal.
       The formula is stored as circularity hypo
  */

  rule [check-hypo-no-hyp-obseq] : 
       <goal>
         <config> 
           <k> checkHypo(SE1:K, SE2:K, .Bag)
                =>
                storeHypo(SE1)
           ...</k>
           <out> OUT1:SExp </out>
         ...</config> 
         <config> 
           <k> break => storeHypo(SE2) ...</k>
           <out> OUT2:SExp </out>
         ...</config>
       ...</goal> 
       when OUT1 ==K OUT2
       [transition]


/*@
  Check hypotheses.
  This is the most tricky step since we have to find a substitution from an
  hypothesis configuration and the current configuration and check that the
  current path (formal) condition implies the formula obtained by applying
  the substitution restrictied to the environment component to the hypothesis
  path formula, as well the formula representing the substitution restricted
  to program (k cell) component.
  Recall that the substitution given by the environment (env cell) is obtained
  with getMapSubst(), and that given by programs is obtained with getSubst().
  Since the configurations in the current formula are unordered, we have 
  to check two cases.

  We consider two additional computational tasks:\\
  computeSubst(Substitution) - that evaluates the components of the given
  substitution in the current environment,\\
  hypoInfo(Bool, Map, Map) - that stores the info about the currently tested
  circular hypothesis; the condiition comoponent of the hypothesis is updated
  with the substitution given by the programs. 
*/


  syntax K ::= computeSubst(Substitution)

  rule computeSubst(X:K replBy E:K)
       =>
       X:K replBy E:K ~> computeSubst(emptySubst)
//       [transition]

  rule computeSubst(X:K replBy E:K ;; S:Substitution)
       =>
       X:K replBy E:K ~> computeSubst(S)
//       [transition]

  rule (X:Int replBy A:Int => .) ~> computeSubst(S:Substitution)
                                 ~> hypoInfo((F':Bool => F' [ A / X ]), _, _)
//       [transition]

  rule <k> (X:Int replBy A:Int => .) ~> computeSubst(S:Substitution) ...</k>
       <k>  computeSubst(S:Substitution) ~> 
           hypoInfo((F':Bool => F' [ A / X ]), _, _)
       ...</k>
//       [transition]

  /*@
  First case: there is substitution between the current configuration
  <c1, c2> /\ F and the hypothesis <c1', c2'> /\ F' and the current configuration
  is included in the observational relation.
  */

  rule [check-hypo] :
       <goal>
         <config> 
           <k> checkHypo(K1:K, Env1:Map, K2:K, Env2:Map, 
     	       		               	     <hypo>      
       					       <hcondition>
					         F':Bool
       					       </hcondition> 
       					       <patt1>        
         				         <hk1>
          					   K1':K 
         					 </hk1> 
         					 <henv1>
          					   Env1':Map
          					 </henv1> 
       					       </patt1> 
       					       <patt2>        
         				         <hk2> 
           					   K2':K
						 </hk2> 
         					 <henv2>
         					   Env2':Map
         					 </henv2> 
       					       </patt2> 
     					     </hypo>
                                             Hypos':Bag
                      )
              =>
             computeSubst(getSubst(K1', K1)) ~> hypoInfo(F', Env1', Env2')
             ~> checkHypo(K1:K, Env1:Map, K2:K, Env2:Map, Hypos')
           ...</k>
           <env> _ => Env1 </env>
         ...</config> 
         <config> 
           <k> break => computeSubst(getSubst(K2', K2)) ~> break ...</k>
           <env> _ => Env2 </env>
         ...</config>
         <condition> F:K </condition>
       ...</goal>
       <observers> Obs:List </observers> 
<debug> Bla => Bla ~> K2SMTLib(filter(F)) ~> getSubst(K1', K1) ~> getSubst(K2', K2) </debug>
       when (eqObs(<env> Env1 </env>, 
                   <env> Env2 </env>,
                   <observers> Obs </observers>, F) ==K true)
       andBool ((isSubst(getSubst(K1', K1)) ==K true)
                 andBool (isSubst(getSubst(K2', K2)) ==K true))
       [transition]
  /*@
  Second case: there is substitution between the current configuration
  <c1, c2> /\ F and the hypothesis <c2', c1'> /\ F' and the current configuration
  is included in the observational relation.
  */

  rule [check-hypo] :
       <goal>
         <config> 
           <k> checkHypo(K1:K, Env1:Map, K2:K, Env2:Map, 
     	       		               	     <hypo>      
       					       <hcondition>
					         F':Bool
       					       </hcondition> 
       					       <patt1>        
         				         <hk1>
          					   K1':K 
         					 </hk1> 
         					 <henv1>
          					   Env1':Map
          					 </henv1> 
       					       </patt1> 
       					       <patt2>        
         				         <hk2> 
           					   K2':K
						 </hk2> 
         					 <henv2>
         					   Env2':Map
         					 </henv2> 
       					       </patt2> 
     					     </hypo>
                                             Hypos':Bag
                      )
            =>
             computeSubst(getSubst(K2', K1)) ~> hypoInfo(F', Env2', Env1')
             ~> checkHypo(K1:K, Env1:Map, K2:K, Env2:Map, Hypos')
           ...</k>
           <env> _ => Env1 </env>
         ...</config> 
         <config> 
           <k> break => computeSubst(getSubst(K1', K2)) ~> break ...</k>
           <env> _ => Env2 </env>
         ...</config>
         <condition> F:K </condition>
       ...</goal>
       <observers> Obs:List </observers> 
<debug> Bla => Bla ~> K2SMTLib(filter(F)) ~>getSubst(K1', K2) ~> getSubst(K2', K1) </debug>
       when (eqObs(<env> Env1 </env>, 
                   <env> Env2 </env>,
                   <observers> Obs </observers>, F) ==K true)
       andBool ((isSubst(getSubst(K1', K2)) ==K true)
                orBool (isSubst(getSubst(K2', K1)) ==K true))
       [transition]


  /*@ The case when the circularity rule can be applied. The goal is removed.
  */

  rule [circularity] :
       (<goal>
         <config> 
           <k> computeSubst(emptySubst) ~>
               hypoInfo(F':Bool, Env1':Map, Env2':Map)
           ...</k>
           <env> Env1:Map </env>
         ...</config> 
         <config> 
           <k> computeSubst(emptySubst) ...</k>
           <env> Env2:Map </env>
         ...</config>
         <condition> F:Bool </condition>
         C:Bag
       </goal>
       =>
       .)
<debug> Bla:K =>  Bla ~> "success" ~> substMap2Bool(getSubstMap(Env1', Env1)) ~> substMap2Bool(getSubstMap(Env2', Env2)) ~> K2SMTLib(filter(F)) ~> K2SMTLib(filter(F')) </debug>
       when (impliesML(Env1, Env2, F, Env1', Env2', F')  ==K true)
       [transition]

  /*@ The case when the circularity rule cannot be applied. The next hypothesis
      is checked.
  */

  rule [circularity-fail] :
       <goal>
         <config> 
           <k>
              computeSubst(emptySubst) ~> hypoInfo(F':Bool, Env1':Map, Env2':Map)
               =>
              .
           ...</k>
           <env> Env1:Map </env>
         ...</config> 
         <config> 
           <k> computeSubst(emptySubst) => . ...</k>
           <env> Env2:Map </env>
         ...</config>
         <condition> F:Bool </condition>
         C:Bag
       </goal>
<debug> Bla:K =>  Bla ~> "fail" ~> substMap2Bool(getSubstMap(Env1', Env1)) ~> substMap2Bool(getSubstMap(Env2', Env2)) ~> K2SMTLib(filter(F)) ~> K2SMTLib(filter(F')) </debug>
       when (impliesML(Env1, Env2, F, Env1', Env2', F')  =/=K true)
       [transition]


  /*@ The rules preparing the storing of an hypothesis. The hypothesis is
  stored in abstract form.
  */
  rule [store-hypo] :
       <config> 
         <k> storeHypo(K1:K) => getFresh(Env1) ~> restore(K1, Env1) ...</k>
         <env> Env1:Map </env>
       </config> 
//       [transition]


  //@ Generates fresh symbolic values for the stored hypothesis
  syntax K ::= "getFresh" "(" Map ")"

  rule [getFresh] :
       <config>
         <k> getFresh(((X:Id |-> _:Int) => .) _ ) ...</k>
         <env>... X |-> (V:Int => VS) ...</env>
       </config>
       <condition> F:Bool => (F andBool (VS ==Int V)) </condition>
       when fresh(VS:Int)

  rule [getFresh] :
       getFresh((X:K |-> V:K => .) _)
       when (isId(X) =/=K true) orBool (isInt(V) =/=K true)

  rule [getFresh] :
       getFresh((#symbMap(_) => .) _)

  rule [getFresh] :
       getFresh((followup(_,_,_) => .) _)

  rule getFresh(.Map) => .K

  syntax K ::= "restore" "(" K "," Map ")"

  rule [restore] :
       <goal>
         <config> 
           <k> restore(K1:K, Env1':Map) => . ...</k>
           <env> Env1:Map => Env1' </env>
         </config> 
         <config> 
           <k> restore(K2:K, Env2':Map) => . ...</k>
           <env> Env2:Map => Env2' </env>
         </config>
         <condition> F:Bool </condition>
       ...</goal>
       <hypos>
         Hypos:Bag
         =>
         Hypos
         <hypo>
           <patt1> 
             <hk1> K1 </hk1>
             <henv1> Env1 </henv1>
           </patt1> 
           <patt2> 
             <hk2> K2 </hk2>
             <henv2> Env2 </henv2>
           </patt2>
           <hcondition> F </hcondition>
         </hypo>
       </hypos>
//      [transition]


  /*@
     The case when both statements are labeled and
     the configurations are NOT observational equal 
  */ 
  rule [store-hypo-fail]:
       <goal>
         <config> 
           <k> lbldStmt(L1:Id, K1:K) => . ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> lbldStmt(L2:Id, K2:K) => . ...</k>
           <env> Env2:Map </env>
         </config>
         <condition> F:K </condition>
       ...</goal>
       <observers> Obs:List </observers>
       when
       (L1 =/=K L2) orBool
       (eqObs(<env> Env1 </env>, 
             <env> Env2 </env>, 
             <observers> Obs </observers>, F) =/=K true)
//       [transition]

/*@
  The following rules are commented  because of the state explosion problem. 
*/ 


/*
  rule [store-hypo-fail]:
       <goal>
         <config> 
           <k> lbldStmt(L1:Id, K1:K) => . ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> lbldStmt(L2:Id, K2:K) ...</k>
           <env> Env2:Map </env>
         </config>
         <condition> F:K </condition>
       ...</goal>
       <observers> Obs:List </observers>
       when
       (L1 =/=K L2) orBool
       (eqObs(<env> Env1 </env> 
             <env> Env2 </env> 
             <observers> Obs </observers>, F) =/=K true)
       [transition]

  rule [store-hypo-fail]:
       <goal>
         <config> 
           <k> lbldStmt(L1:Id, K1:K) ...</k>
           <env> Env1:Map </env>
         </config> 
         <config> 
           <k> lbldStmt(L2:Id, K2:K) => . ...</k>
           <env> Env2:Map </env>
         </config>
         <condition> F:K </condition>
       ...</goal>
       <observers> Obs:List </observers>
       when
       (L1 =/=K L2) orBool
       (eqObs(<env> Env1 </env> 
             <env> Env2 </env> 
             <observers> Obs </observers>, F) =/=K true)
       [transition]
*/

/*@
  The following rule creates the initial configuration from the equivalence
  specification given as input.
*/

  rule [initial] :
       <config>
         <k> 
           <k> P1:Stmt </k>
           <env> Inits1:InitVals </env>
           ~
           <k> P2:Stmt </k>
           <env> Inits2:InitVals </env>
           if F:BExp
           using observers: Obs:Ids; 
           =>
           setInitVal(Inits1) ~> setInitValObs(Obs) ~> P1
         </k>
       ...</config>
       <condition> _ => injectForm(F) </condition>
      (. =>
       <config>
         <k> 
           setInitVal(Inits2) ~> setInitValObs(Obs) ~> P2
         </k>
         <env> . </env>
       </config>)
       <observers> . => Ids2List(Obs) </observers>

/*@
  The auxiliary construct \texttt{initVal()} is used for initializing the 
  observer variables with the same values in the two initial program
  configurations. 
*/


  syntax K ::= "setInitVal" "(" InitVals ")"

  rule setInitVal(.InitVals) => .
       [structural]

  rule <k> setInitVal((X:Id -> V:Int, XVs:InitVals) => XVs) ...</k>
       <env>... . => X |-> V ...</env>
       [structural]

  rule <k> setInitVal((SymMap(M:Id), XVs:InitVals) => XVs) ...</k>
       <env>... . => #symbMap(M) ...</env>
       [structural]

  syntax K ::= "setInitValObs" "(" Ids ")"

  rule <k> setInitValObs(.Ids) => . ...</k>
       <k> setInitValObs(.Ids) => . ...</k>
       [structural]

  rule <k> setInitValObs(allObs) => . ...</k>
       <k> setInitValObs(allObs) => . ...</k>
       [structural]

  /*@ The values for observers must be different, in order to correctly 
      define substitution.
  */

  rule <config>
         <k> setInitValObs((X:Id, Xs:Ids) => Xs) ...</k>
         <env> Env:Map (. => X |-> IS1) </env>
       </config> 
       <config> 
         <k> setInitValObs((X:Id, Xs:Ids) => Xs) ...</k>
         <env>... . => X |-> IS2 ...</env>
       </config> 
       <condition> B:K => B andBool (IS1 ==Int IS2) </condition>
       when (fresh(IS1:Int) andBool fresh(IS2:Int)) andBool notBool(X in keys(Env))
       [structural]

  rule <config>
         <k> setInitValObs((X:Id, Xs:Ids) => Xs) ...</k>
         <env> Env:Map </env>
       </config> 
       when (X in keys(Env))
       [structural]

/*@ 
  The next function translates the initial condition into internal
  form.\\
  TBD: refactor it!!!!
*/


  syntax Bool ::= "injectForm" "(" BExp ")" [function]

  rule injectForm(true) => true

  rule injectForm(A1:AExp == A2:AExp)
       =>
       injectAExp(A1)  ==Int injectAExp(A2)


  rule injectForm(B1:BExp and B2:BExp)
       =>
       injectForm(B1) andBool injectForm(B2)


  rule injectForm(not B:BExp)
       =>
       notBool injectForm(B)


  syntax Int ::= "injectAExp" "(" AExp ")" [function]
  rule injectAExp(I:Int) => I
  rule injectAExp(A1:AExp + A2:AExp)
       =>
       injectAExp(A1)  +Int injectAExp(A2)


  rule injectAExp(A1:AExp * A2:AExp)
       =>
       injectAExp(A1)  *Int injectAExp(A2)


  rule injectAExp(A1:AExp / A2:AExp)
       =>
       injectAExp(A1)  /Int injectAExp(A2)


  rule injectForm(X:Id isNotModifiedBy S:Stmt ) 
       =>
       X isNotModifiedBy S

  rule injectForm(X:AExp isNotModifiedBy S:Stmt ) 
       =>
       X isNotModifiedBy S

  rule injectForm(X:BExp isNotModifiedBy S:Stmt ) 
       =>
       X isNotModifiedBy S


/*@
  The following is a helper function that transform a list of
  identifiers into a builtin list; it is used for storing the observer
  variables into the cell \texttt{observers}.
*/ 
  syntax List ::= "Ids2List" "(" Ids ")" [function]
  rule Ids2List(.Ids) => .List
  rule Ids2List(X:Id, Xs:Ids) => ListItem(X) Ids2List(Xs)


 

endmodule
