load ../../../../k-prelude
load ../../substitution/substitution
kmod LAMBDA-CALL-BY-NEED is  including SUBSTITUTION +  K-STRICTNESS
  syntax Exp ::= Val
               | Exp Exp [strict (1)]
  syntax Val ::= lambda BoundingExp
  context (lambda(_->[HOLE]))_
---  context X:Id ~> ?:K ~> freezer("'__('lambda_('_->_(Id?4:Id(.List{K}),,`[HOLE`]:K)),,?5:K)")(freezeVar("?4:Id")(X),,freezeVar("?5:K")(`[HOLE`]:K))
  context (lambda(X._[[X]]))[HOLE]

  rule [deref] : (lambda(X->_[[X => alpha(V)]])) V
  rule [lift] : (lambda(X:Id->A:Exp)M:Exp)N:Exp => (lambda(X->(A N)))M
    if isAnswer(A) [structural] 
  rule [assoc] : (lambda(X->E[[X]]))((lambda(Y->A))M)
              => (lambda(Y->(lambda(X->E[[X]])) A)) M
    if isAnswer(A) [structural]
  
  syntax Bool ::= isAnswer ( Exp )
  syntax K ::= Bool
  rule isAnswer(lambda _) => true [structural]
  rule isAnswer((lambda(_->A))_) => isAnswer(A) [structural]
endkm
