// Copyright (c) 2013-2014 K Team. All Rights Reserved.

require "builtins/symbolic-k.k"


/*!
\setlength{\parindent}{1em}

\newcommand{\IMP}{\textsc{imp}\xspace}
\newcommand{\STREAM}{\textsc{stream}\xspace}

\title{SEQ (Program Equivalence on \STREAM)}
\author{Dorel Lucanu (\texttt{dlucanu@info.uaic.ro})}
\organization{Alexandru Ioan Cuza University of Ia\c{s}i, Romania}
\newcommand{\pattern}[2]{{#1}%
  \ifthenelse{\equal{#2}{}}{}{%
    \,{\pmb{\wedge}}\,{#2}%
  }%
}
*/


//@ \section{Syntax}

module STREAM-SYNTAX

  //@ Boolean Expressions

  syntax BExp ::= Bool
                | IExp "=" IExp [strict]
                | "!" BExp [strict]
                | BExp "&" BExp [strict(1)]

  //@ Integer Expressions
  syntax IExp ::=  Int | Id
                | "hd" "(" SExp ")" [strict]
                | "(" IExp ")" [bracket]
                > Id "(" IExps ")" [strict(2)]
                > IExp "<|" BExp "|>" IExp [strict(2)]
                | IExp "+" IExp [strict]

  syntax IExps ::= List{IExp,","} [strict]
  //@ Stream Expressions


  syntax SExp ::= Id
                | "tl" "(" SExp ")" [strict, prefer]
                | "(" SExp ")" [bracket]
                > Id "(" SExps ")" [strict(2)]
                > Id "." SExp [strict(2), lsexp]
                > IExp ":" SExp [strict(1), right, constr]
                | "[]"

  syntax SExps ::= List{SExp,","} [strict]


  //@ Expressions
  syntax Exp ::= IExp | SExp
  syntax Exps ::= List{Exp,","} [strict]


  //@ Stream Specifications
  syntax SSpec ::= Id ":~" Exp ";"
                 | Id "(" Ids ")" ":~" Exp ";"
                 | Id ":=" IExp ";"
                 | Id "(" Ids ")" ":=" IExp ";"
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

  syntax EqvPgms ::= EqvPgm | EqvPgms EqvPgms [left]

  syntax Start ::= EqvPgms


  /*@
    Extending with symbolic values:
   */

/*
  syntax IExp ::= "#symIExp" "(" Id ")"  [onlyLabel, klabel(#symIExp)]

  syntax SExp ::= "#symSExp" "(" Id ")"  [onlyLabel, klabel(#symSExp)]

  syntax Int ::= "#symInt" "(" Id ")" [onlyLabel, klabel(#symInt)]
*/
  //@ Variables

  syntax VariableSExp ::= Token{[\$][A-Z][a-zA-Z0-9]*[\:][S][E][x][p]} [onlyLabel]
  syntax VariableBSExp ::= Token{[\$][A-Z][a-zA-Z0-9]*[\:][B][S][E][x][p]} [onlyLabel]

  syntax SExp ::= VariableSExp
  syntax VariableSExp ::= VariableBSExp

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
i.e., of the form $(\exists X)\pattern{\overline{\pi}'}{\phi'\land \sigma}$,
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



  rule getSubst(#symSExp(X:K), SE:SExp) => (#symSExp(X) replBy SE)

  rule getSubst(#symInt(X:K), IE:IExp) => (#symInt(X) replBy IE)

  rule getSubst(V:VariableSExp, SE:SExp) => (V replBy SE)

  rule getSubst(V:VariableBSExp, SE:SExp) => (V replBy SE)

  rule getSubst(hd(SE:SExp), hd(SE':SExp)) => getSubst(SE, SE')

  rule getSubst(tl(SE:SExp), tl(SE':SExp)) => getSubst(SE, SE')

  rule getSubst(F:Id(SEs:SExps), F(SEs':SExps)) => getSubst(SEs, SEs')

  rule getSubst(IE:IExp : SE:SExp, IE':IExp : SE':SExp)
       => getSubst(IE, IE') ;; getSubst(SE, SE')

  rule getSubst((SE:SExp, SEs:SExps), (SE':SExp, SEs':SExps))
       => getSubst(SE, SE') ;; getSubst(SEs, SEs')

  rule getSubst(.SExps, .SExps) => emptySubst

  rule getSubst(E, E) => emptySubst

  // to be completed


/*@
  Check if a Substitution is indeed a substitution:
*/

  syntax K ::= "isSubst" "("  K ")"  [function]

  rule isSubst(emptySubst) => true

  rule isSubst(I:K replBy A:K) => true

  rule isSubst(M:K ;; (I:K replBy A:K)) => isSubst(M)

  // to be refactored

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

  rule eqObs(<out> OUT:SExp </out>,
             <out> OUT </out>)
       =>
       true
*/
/*
  It is easier to test OUT1 ==K OUT2 each time we need to compute the
  observability relation.
*/

  //@ \section{Auxiliary Operations}

  //@ Substitution

  syntax Exp ::= Exp "[" Exps "/" Ids "]" [function]

  rule SE:Exp[(V:SExp, (V':Exp, Vs:Exps)) / (X:Id, (X':Id, Xs:Ids))]
       =>
      (replace(X, V, SE))[(V', Vs) / (X', Xs)]

  rule SE:Exp[(V:Exp, .Exps) / (X:Id, .Ids)] => replace(X, V, SE)


  //@ Append

  syntax SExp ::= append(Int, SExp) [function]

  rule append(I:Int, []) => I : []
  rule append(I:Int, J:Int : SE:SExp) => J : append(I, SE)


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


  syntax Bool ::= isInstanceOfSExp(SExp, SExp) [function]

  rule isInstanceOfSExp(_:SExp, []) => true
  rule isInstanceOfSExp(IE:IExp : SE:SExp, IE : SE':SExp)
       =>
       isInstanceOfSExp(SE, SE')


  //@ removing the labels from an stream expression

  syntax SExp ::= removeLabels(SExp) [function]

/*
  syntax SExp ::= Id
                | "tl" "(" SExp ")" [strict, prefer]
                | "(" SExp ")" [bracket]
                > Id "(" SExps ")" [strict(2)]
                > Id "." SExp [strict(2), lsexp]
                > IExp ":" SExp [strict(1), right, constr]
                | "[]"
*/
  rule removeLabels(X:Id) => X
  rule removeLabels(V:VariableSExp) => V
  rule removeLabels(tl(SE:SExp)) => tl(removeLabels(SE))
  rule removeLabels(X:Id(SEs:SExps)) => X(removeLabels(SEs))
  rule removeLabels(_:Id . SE:SExp) => removeLabels(SE)
  rule removeLabels(_:IExp : SE:SExp) => removeLabels(SE)

  syntax SExp ::= removeLabels(SExps) [function]

  rule removeLabels(SE:SExp, SEs:SExps) => removeLabels(SE), removeLabels(SEs)
  rule removeLabels(.SExps) => .SExps

endmodule

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
                        <k color="green"> $PGM:EqvPgms  </k>
                        <sspecs color="red"> .Map </sspecs>
                        <out> [] </out>
                      </config>
                      <kb> .Map </kb>
                    </goal>
                  </goals>
                  <hypos>
                    <hypo multiplicity="*">
                      <patt1>
                        <hk1 color="green"> .K  </hk1>
                        <hout1> [] </hout1>
                      </patt1>
                      <patt2>
                        <hk2 color="green"> .K  </hk2>
                        <hout2> [] </hout2>
                      </patt2>
                    </hypo>
                  </hypos>
                </T>

 //@ The right-hand side of a specification is stored as a $\lambda$-expression:
  syntax KItem ::= "lambda" "(" Ids ")" Exp

/*@ The result values are integers and stream expression for that at  least
  the head is evaluated to an integer:
*/
  syntax KResult ::= Int | Bool


  rule isKResult(_:Int : _:SExp) => true
  rule isKResult('_._(_:Id ,, _:Int : _:SExp)) => true


  //@ Preprocessing

  rule <goal>
         <config> <k> EP:EqvPgm EPs:EqvPgms </k> Cfg:Bag </config>
         Cfg':Bag
       </goal>
       =>
       <goal> <config> <k> EP </k> Cfg </config> Cfg' </goal>
       <goal> <config> <k> EPs </k> Cfg </config> Cfg' </goal>

  rule SS:SSpec SSs:SSpecs E:Exp => SS ~> SSs E

  rule (SS:SSpec E:Exp) => SS ~> E

  rule <k> F:Id :~ SE:SExp; => . ...</k>
       <sspecs>... . => F |-> lambda(.Ids) SE </sspecs>


  rule <k> F:Id(Ys:Ids) :~ SE:SExp; => . ...</k>
       <sspecs>... . => F |-> lambda(Ys) SE </sspecs>

  rule <k> F:Id := IE:IExp; => . ...</k>
       <sspecs>... . => F |-> lambda(.Ids) IE </sspecs>

  rule <k> F:Id(Ys:Ids) := IE:IExp; => . ...</k>
       <sspecs>... . => F |-> lambda(Ys) IE </sspecs>

 // cotext

  context '_._(_:Id ,, HOLE : _:SExp)

 //@ Computations:

  rule I1:Int = I2:Int => I1 ==Int I2

  rule ! B:Bool => notBool B

  rule true & BE:BExp => BE

  rule false & _:BExp => false

  rule IE:IExp <| true |> _:IExp => IE

  rule _:IExp <| false |> IE:IExp => IE

  // only for bit streams

  rule <k> V:VariableBSExp => 0 : V ...</k>
       <kb> KB:Map => (KB V |-> (0 : V)) </kb>
       requires notBool V in keys(KB)
       [transition]

  rule <k> V:VariableBSExp => 1 : V ...</k>
       <kb> KB:Map => (KB V |-> (1 : V)) </kb>
       requires notBool V in keys(KB)
       [transition]

  rule <k> V:VariableBSExp => SE ...</k>
       <kb>... V |-> SE:SExp  ...</kb>


 //@ The evaluation of the head:

  rule hd(I:Int : _) => I [anywhere]
  rule hd('_._(_:Id ,, I:Int : _)) => I [anywhere]

  //@ The evaluation of tail:

  rule tl(_:Int : SE:SExp) => SE [anywhere]
  rule tl('_._(_:Id ,, _:Int : SE:SExp)) => SE [anywhere]

  //@ When the head is completely evaluated is moved in the cell out:
  rule <k> I:Int => . </k>
       <out> SE:SExp => append(I, SE) </out>

  rule <k> I:Int : SE:SExp => SE </k>
       <out> OUT:SExp => append(I, OUT) </out>

 //@ Stream specification without parameters:

  rule <k> F:Id => SE ...</k>
       <sspecs>... F |-> lambda(.Ids) SE ...</sspecs>
       [transition]

  rule <k> V:VariableSExp => SE ...</k>
       <sspecs>... V |-> lambda(.Ids) SE ...</sspecs>
       [transition]

 //@ Stream specification with parameters:

  rule <k> F:Id(SEs:SExps) => SE[SEs / Xs] ...</k>
       <sspecs>... F |-> lambda(Xs:Ids) SE:SExp ...</sspecs>
       [transition]

  rule <k> F:Id(IEs:IExps) => IE[IEs / Xs] ...</k>
       <sspecs>... F |-> lambda(Xs:Ids) IE:IExp ...</sspecs>
       [transition]


  //@ The semantics of the new introduced labelled expressions:

  rule [labelled-sexp] :
       <k>
          ( L:Id . SE:SExp
            =>
            lbldStmt(L, SE) ~> SE // ~> K) ~> SE
          ) // ~> K:K
       </k>



/*@
  The next rule implements the basic entailment relation. The current version
  is incomplete because we have to show it is sound on the tested (it is depending on
  hpw the observation relation is defined).
  We have to elaborate the implementation of the basic
  entailment.
*/

  rule [basic-entailment] :
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
       ...</goal>
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
  We use a new syntactic construct that help us to store hypotheses. The basic
  idea is to add the hypotheses in a controlled way. For instance, we may add
  hypothesis only when on the top in the two k cells we have  statement with
  the same label (the label is a kind of "rendevous" synchronisarion).
*/

  syntax KItem ::= "storeHypo" "(" K ")"   // for storing hypotheses
                |  "lbldStmt" "(" Id "," K ")"    // event signalling a labelled
                                                  // statement
                |  "checkHypo" "(" K ","  K "," HyposCellFragment ")"
                   // for checking hypotheses one by one

  syntax KItem ::= "break"  // to temporarily stop one of the two programs


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
           <k> lbldStmt(L:Id, SE1:K) => checkHypo(SE1, SE2, Hypos) ...</k>
           <sspecs> SSp1:Map </sspecs>
           <out> OUT1:SExp </out>
         </config>
         <config>
           <k> lbldStmt(L:Id, SE2:K) => break ...</k>
           <sspecs> SSp2:Map </sspecs>
           <out> OUT2:SExp </out>
         </config>
       ...</goal>
       <hypos>
         Hypos:Bag
       </hypos>


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

*/

  /*@
  First case: there is substitution between the current configuration
  <c1, c2> /\ F and the hypothesis <c1', c2'> /\ F' and the current configuration
  is included in the observational relation.
  */

  rule [check-hypo] :
       (<goal>
         <config>
           <k> checkHypo(SE1:K, SE2:K,
                                       <hypo>
                              <patt1>
                              <hk1>
                             SE1':K
                          </hk1>
                          <hout1>
                             OUT1':SExp
                           </hout1>
                              </patt1>
                              <patt2>
                             <hk2>
                             SE2':K
                     </hk2>
                          <hout2>
                            OUT2':SExp
                          </hout2>
                              </patt2>
                          </hypo>
                                     Hypos':Bag
                      )
           ...</k>
           <out> OUT1 </out>
         ...</config>
         <config>
           <k> break ...</k>
           <out> OUT2 </out>
         ...</config>
       ...</goal>
       =>
// <goal> <config> <k> getSubst(SE1', SE1) ~> getSubst(SE2', SE2) </k> </config> <sspecs> .Map </sspecs> <out> [] </out> </goal> ) // for debugging
       .)
       when (OUT1 ==K OUT2)
       andBool (isSubst(getSubst(SE1', removeLabels(SE1))) ==K true)
       andBool (isSubst(getSubst(SE2', removeLabels(SE2))) ==K true)
       andBool isInstanceOfSExp(OUT1, OUT1') ==K true
       andBool isInstanceOfSExp(OUT2, OUT2') ==K true
       [transition]
  /*@
  Second case: there is substitution between the current configuration
  <c1, c2> /\ F and the hypothesis <c2', c1'> /\ F' and the current configuration
  is included in the observational relation.
  */

  rule [check-hypo] :
       (<goal>
         <config>
           <k> checkHypo(SE1:K, SE2:K,
                                       <hypo>
                              <patt1>
                              <hk1>
                             SE1':K
                          </hk1>
                          <hout1>
                             OUT1':SExp
                           </hout1>
                              </patt1>
                              <patt2>
                             <hk2>
                             SE2':K
                     </hk2>
                          <hout2>
                            OUT2':SExp
                          </hout2>
                              </patt2>
                          </hypo>
                                     Hypos':Bag
                      )
           ...</k>
           <out> OUT1 </out>
         ...</config>
         <config>
           <k> break ...</k>
           <out> OUT2 </out>
         ...</config>
       ...</goal>
       =>
// <goal> <config> <k> getSubst(SE2', SE1) ~> getSubst(SE1', SE2) </k> </config> <sspecs> .Map </sspecs> <out> [] </out> </goal>) // for debugging
      .)
       when (OUT1 ==K OUT2)
       andBool (isSubst(getSubst(SE2', removeLabels(SE1))) ==K true)
       andBool (isSubst(getSubst(SE1', removeLabels(SE2))) ==K true)
       andBool isInstanceOfSExp(OUT1, OUT2') ==K true
       andBool isInstanceOfSExp(OUT2, OUT1') ==K true
       [transition]

  rule [check-hypo] :
       <goal>
         <config>
           <k> checkHypo(SE1:K, SE2:K,
                                      (<hypo>
                              <patt1>
                              <hk1>
                             SE1':K
                          </hk1>
                          <hout1>
                             OUT1':SExp
                           </hout1>
                              </patt1>
                              <patt2>
                             <hk2>
                             SE2':K
                     </hk2>
                          <hout2>
                            OUT2':SExp
                          </hout2>
                              </patt2>
                          </hypo>
                                     =>
                                     .)
                                    Hypos':Bag
                      )
           ...</k>
           <out> OUT1 </out>
         ...</config>
         <config>
           <k> break ...</k>
           <out> OUT2 </out>
         ...</config>
       ...</goal>
       when (isSubst(getSubst(SE1', removeLabels(SE1))) =/=K true)
       orBool (isSubst(getSubst(SE2', removeLabels(SE2))) =/=K true)
       orBool isInstanceOfSExp(OUT1, OUT1') =/=K true
       orBool isInstanceOfSExp(OUT2, OUT2') =/=K true
       [transition]


  /*@ The rules preparing the storing of an hypothesis. The hypothesis is
  stored in abstract form.
  */
  rule [store-hypo] :
       <config>
         <k> storeHypo(K1:K) => restore(K1) ...</k> // just for conformance
       ...</config>
//       [transition]


  syntax KItem ::= "restore" "(" K ")"

  rule [restore] :
       <goal>
         <config>
           <k> restore(K1:K) => . ...</k>
             <out> OUT1 </out>
         ...</config>
         <config>
           <k> restore(K2:K) => . ...</k>
             <out> OUT2 </out>
         ...</config>
       ...</goal>
       <hypos>
         Hypos:Bag
         =>
         Hypos
         <hypo>
           <patt1>
             <hk1> removeLabels(K1) </hk1>
             <hout1> OUT1 </hout1>
           </patt1>
           <patt2>
             <hk2> removeLabels(K2) </hk2>
             <hout2> OUT2 </hout2>
           </patt2>
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
           <out> OUT1:SExp </out>
         ...</config>
         <config>
           <k> lbldStmt(L2:Id, K2:K) => . ...</k>
           <out> OUT2:SExp </out>
         ...</config>
       ...</goal>
       when
       (L1 =/=K L2) orBool
       (OUT1 =/=K OUT2)
//       [transition]

/*@
  The following rule creates the initial configuration from the equivalence
  specification given as input.
*/

  rule [initial] :
       <config>
         <k>
           <k> SE1:SExp </k>
           <sspecs> SSs1:SSpecs </sspecs>
           ~
           <k> SE2:SExp </k>
           <sspecs> SSs2:SSpecs </sspecs> ;
           =>
           SSs1 SE1
         </k>
       ...</config>
      (. =>
       <config>
         <k> SSs2 SE2 </k>
         <sspecs> .Map </sspecs>
         <out> [] </out>
       </config>)

endmodule
