# Design
The overall design of the new sort inference algorithm (`SortInferencer.java`) is based on the paper [The Simple Essence of Algebraic Subtyping: Principal Type Inference with Subtyping Made Easy](https://infoscience.epfl.ch/record/278576) by Lionel Parreaux. We summarize the relevant parts below, but it's a short and enlightening paper that's worth reading if you want a deeper understanding.

## SimpleSub Summary
The SimpleSub paper describes a type inference algorithm for a lambda calculus with sub-typing. The type system is akin in expressiveness to something like Java-generics, i.e., permitting type variables `𝛼` with bounds `L <: 𝛼 <: U` (`super` and `extends` in Java).

Notably though, it captures this expressiveness with a very simple type semantics, enabling inferred subtyping constraints to be efficiently reduced to constraints on type variables (e.g. by mutating a type variable's sub-/super-type bounds throughout the inference process). As well, the results are expressed using "set-theoretic" types, which allow the type constraints to be recorded in an indirect, compact form while also making certain type-simplifications more obvious.

The inferred types have the following syntax
```
𝜏 ::= primitive                  // built-ins
    | 𝜏 → 𝜏                      // functions
    | { 𝑙0 : 𝜏 ; ...; 𝑙𝑛 : 𝜏 }    // structurally-typed records (won't be relevant for us)
    | 𝛼                         // type variables
    | ⊤                         // top type which is a supertype of all others
    | ⊥                         // bottom type which is a subtype of all others
    | 𝜏 ⊔ 𝜏                     // type unions / joins
    | 𝜏 ⊓ 𝜏                     // type intersections / meets
    | 𝜇𝛼.𝜏                      // recursive types (won't be relevant for us)
````
which is additionally subject to a *polarity* restriction. Informally, for a type `𝜏` which is a syntactic subcomponent of some other type `T`, the polarity of `𝜏` is
- *negative*, if `𝜏` describes a value given as an input to a term with type `T`
- *positive*, if `𝜏` describes a value produced by a term with type `T`

As a concrete example, in a type like `(𝜏0 → 𝜏1) → 𝜏2`,
- `𝜏2` is positive, as the term produces the value of type `𝜏2` as an output 
- `𝜏0 → 𝜏1` is negative, as the value of this type is given as an input to the term
- `𝜏1` is negative, as the value of this type is also given as an input to the term (indirectly via the input function `𝜏0 → 𝜏1`)
- `𝜏0` is positive, as the term itself must produce this value in order to call the input function `𝜏0 → 𝜏1`

More formally, we define the type as a whole to be positive, and say
- `𝜏` is negative if either
    - it occurs as the left part of an arrow `𝜏 → 𝜏'` where `𝜏 → 𝜏'` is itself positive, or
    - it occurs as the right part of an arrow `𝜏' → 𝜏` where `𝜏' → 𝜏` is itself negative
- `𝜏` is positive otherwise

The polarity restriction on our type syntax then requires that
- type intersections `𝜏 ⊓ 𝜏` may only occur in negative position
- type unions `𝜏 ⊔ 𝜏` may only occur in positive position

To understand the motivation for this restriction, consider the subtyping constraints in a program and observe that
- if a type `𝜏` is negative, then it corresponds to an upper bound - the term requires a `𝜏` as input, and therefore can accept any sub-type of `𝜏`
- if a type `𝜏` is positive, then it corresponds to a lower bound - the term produces a `𝜏` as output, which can then be used at any place where some supertype of `𝜏` is expected

Informally then, the polarity restriction enforces that type intersections can only be used for upper bounds and type unions can only be used for lower bounds. In fact, there is an exact correspondence, as conversely any upper/lower bounds can always be encoded by a type intersection/union:
- `𝜏 <: 𝜏1 and 𝜏 <: 𝜏2 iff 𝜏 <: 𝜏1 ⊓ 𝜏2`
- `𝜏1 <: 𝜏 and 𝜏2 <: 𝜏 iff 𝜏1 ⊔ 𝜏2 <: 𝜏`

In total then, any type variable with bounds `L <: 𝛼 <: U` can be encoded as a set-theoretic type by 
- replacing every negative instance of `𝛼` with `𝛼 ⊓ U` 
- replacing every positive instance of `𝛼` with `𝛼 ⊔ L`

Conversely, any set-theoretic type subject to the polarity restriction can be converted back to type variables with bounds by iteratively applying this process in reverse, i.e.,
- replacing every intersection involving a type variable `𝛼 ⊓ U` with `𝛼` and recording the bound `𝛼 <: U` (introducing a fresh type variable for intersections involving only concrete types)
- replacing every union involving a type variable `𝛼 ⊔ L` with `𝛼` and recording the bound `L <: 𝛼` (introducing a fresh type variable for unions involving only concrete types)

For example, consider a term like
```
𝜆𝑥 . { L = 𝑥 − 1 ; R = if 𝑥 < 0 then 0 else 𝑥 }
 ```
where `nat <: int`, `- : int → int → int`, and `0 : nat`. 

Prior to some simplification passes, SimpleSub will infer the type
```
𝛼 ⊓ int → { L : int ; R : 𝛽 ⊔ nat ⊔ 𝛼 }
```
which corresponds to the Java-esque type
```
⟨𝛼 extends int, 𝛽 super nat | 𝛼⟩(𝛼) → { L : int ; R : 𝛽 }
```
After simplification, SimpleSub will produce the final type
```
𝛼 ⊓ int → { L : int ; R : nat ⊔ 𝛼 }
```
which corresponds to the Java-esque type
```
⟨𝛼 super nat extends int⟩(𝛼) → { L : int ; R : 𝛼 }
```

### Inference Algorithm
With this background understood, the actual algorithm is quite simple. Below, I provide the algorithms from the paper in Scala with all the parts that are irrelevant to us removed (namely records, let-bindings, and recursive types).

Take our AST as follows:
```
enum Term {
case Lit (value: Int)
case Var (name: String)
case Lam (name: String, rhs: Term)
case App (lhs: Term, rhs: Term)
}
```
The first step is to produce a `SimpleType` which directly records bounds for each variable:
```
enum SimpleType {
case Variable (st: VariableState)
case Primitive (name: String)
case Function (lhs: SimpleType, rhs: SimpleType)
}

class VariableState(var lowerBounds: List[SimpleType],
                    var upperBounds: List[SimpleType])
```
The algorithm proceeds straightforwardly, noting type constraints at each function application:
```
def typeTerm(term: Term)(implicit ctx: Map[String, SimpleType]): SimpleType = term match {
case Lit(n) => Primitive("int")
case Var(name) => ctx.getOrElse(name, err("not found: " + name))
case Lam(name, body) =>
  val param = freshVar
  Function(param, typeTerm(body)(ctx + (name -> param)))
case App(f, a) =>
  val res = freshVar
  constrain(typeTerm(f), Function(typeTerm(a), res))
  res
}
```
The constrain function propagates the newly found sub-typing constraint in a manner that ensures coherence with all previously recorded constraints:
```
def constrain(lhs: SimpleType, rhs: SimpleType)
     (implicit cache: MutSet[(SimpleType, SimpleType)]): Unit = {
if (cache.contains(lhs -> rhs)) return () else cache += lhs -> rhs
(lhs, rhs) match {
  case (Primitive(n0), Primitive(n1)) if subtype(n0, n1) => () // nothing to do
  case (Function(l0, r0), Function(l1, r1)) =>
    constrain(l1, l0); constrain(r0, r1)
  case (Variable(lhs), rhs) =>
    lhs.upperBounds = rhs :: lhs.upperBounds
    lhs.lowerBounds.foreach(constrain(_, rhs))
  case (lhs, Variable(rhs)) =>
    rhs.lowerBounds = lhs :: rhs.lowerBounds
    rhs.upperBounds.foreach(constrain(lhs, _))
  case _ => err("cannot constrain " + lhs + " <: " + rhs)
}}
```
Once the `SimpleType` is inferred, we then go through the process described before of encoding the typing constraints as unions or intersections of the bounds. The end result is a `CompactType`, which denotes either a union or intersection of its contained types depending on the polarity where it occurs:

```
case class CompactType(vars: Set[TypeVariable],
                       prims: Set[PrimType],
                       fun: Option[(CompactType, CompactType)])
```
The implementation of the compact function is straightforward and omitted here.

We then perform two simplifications on these `CompactTypes` to remove unnecessary parametricity. We say that two type variables *co-occur* if they appear in the same union or intersection. The two simplifications are then as follows: 

- If a type variable `𝛼` always co-occurs positively with some other type variable `β` and vice-versa, then  `𝛼` and `β` can be unified. The same applies for negative occurrences. For example, the obvious type for an `if-then-else` function `bool → 𝛼 → β → 𝛼 ⊔ β` is in fact equivalent to `bool → 𝛼 → 𝛼 → 𝛼`.

- If a type variable `𝛼` always co-occurs both positively and negatively with some other type `T`, then `𝛼` can be removed. For example, `𝛼 ⊓ Int → 𝛼 ⊔ Int` is the same as `Int → Int`

See the paper for an explanation of why these simplifications are justified.

The final step of the algorithm is to coalesce each `CompactType` into the final set-theoretic type syntax described initially. Ignoring recursive types, this is just an easy syntactic transformation, so we omit the implementation here (it's also unneeded for our use cases).

## From SimpleSub To Sort Inference

To begin, consider the simplified setting of terms without ambiguities or parametric sorts.

The conceptual translation from K `Term`s to the SimpleSub language is straightforward.

First, given `pr` a `ProductionReference`  whose id is `prId`, sort is `S`, non-terminal sorts are `S1, ..., SK`, and items are `t1, ..., tK`, we note that the typing constraints it induces are the same as any function symbol, so we let
```
translateBody(pr) = prId translateBody(t1) ... translateBody(tK)
```
where
```
prId : S1 → ... → SK → S
```
is taken as a built-in in the SimpleSub language. 

Then, given `t` any `Term` containing variables `x1, ..., xN`, define the translation
```
translate(t) = 𝜆x1. ... 𝜆xN. translateBody(t)
```

When we perform type inference on `translate(t)`, we will obtain a function type of the form `T1 → ... → TN → T`. This tells us that `x1 : T1`, ..., `xN : TN`, and, `term : T`, exactly as needed for sort inference! 

There are a few final caveats, which can be easily addressed:
- In K, we do not actually have a complete type lattice, and the intersections and unions of sorts may not actually exist. If we produce a type with such non-existent sorts, it is simply a type error.
- We do not yet support parametric rules throughout K, and may not ever support bounds on parametric sort variables (although this is something to consider!). We can address this by just monomorphizing with every sort in the poset that satisfies the appropriate bounds for each variable. These different monomorphizations should correspond one-to-one with the different maximal models found in the Z3-based sort inference engine.
- Function, macro, and anywhere rules must be special-case. Conceptually, we can just think of these as a `ProductionReference` to some specialized `KRewrite` whose return sort is exactly the declared sort of the LHS.
- Strict casts require us to unify rather than introduce subtyping constraints.

### Ambiguities
To extend the idea above to handle ambiguities, we note that any parse tree can be divided into unambiguous sub-trees (which we call *slices* in the implementation). The high-level idea is to infer a type for each slice parametric over its contained ambiguities.

Explicitly, given `t` a `Term` thought of as a tree/AST, cut `t` at each ambiguity node. This will produce a number of sub-trees trees, each of whose root node is either the root of `t` or the direct child of some `Ambiguity` occurring in `t`, and each of whose leaves are either a `Constant` or `Ambiguity`.

Given such a slice `t` containing `Ambiguity` nodes with which we associate identifiers `amb1, ..., ambK`, and presuming our overall term contains the variables `x1, ..., xN`, let
```
translateSlice(t) =  𝜆amb1. ... 𝜆ambK. 𝜆x1. ... 𝜆xN. translateBody(t)
```
and extend `translateBody` as above with the rule
```
translateBody(ambi) = ambi x1 ... xN
```
The intuition here is that our translation shows that any `Term` corresponds to a SimpleSub function abstracted over all the contrained variables, so an ambiguity can just be represented as some function variable (whose concrete types are not yet known) which is applied to all these variables.

When we perform inference on `translateSlice(t)`, the resulting type will have the form
```
(A11 → ... → A1N → A1)  → ... → (AK1 → ... → AKN → AK) → T1 → ... → TN → T`.
```
Here, each `Ai` indicates the expected type of the `Ambiguity` associated to the identifier `ambi`.

If an ambiguity's child does not itself contain ambiguities (as will always be true far enough down in the parse tree), we can "fold" that particular child into the type of the parent slice by simple function application, corresponding to choosing that child of the ambiguity for our final parse. 

Specifically, let `t` be the term as above and `c` its child slice. We can infer the type of the function application `translateSlice(t) translateSlice(c)` and will be left with either a type error or a type of the form
```
(A21 → ... → A2N → A1)  → ... → (AK1 → ... → AKN → AK) → T1' → ... → TN' → T'`.
```
which is the specialization of `translateSlice(t)`'s type when picking `c` as the value of the ambiguity. 

We can use this process to then iteratively collapse the tree of slices along all possible paths, starting from the leaves upward. Those paths that encounter type errors during substitution are pruned, while the others are collected into a set of all possible parses along with their inferred types. Unfortunately, this is `O(2^N)` in the worst case, but the hope is that the actual factors involved will be small.
