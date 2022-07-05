# Lesson 1.22: Basics of Deductive Program Verification using K

In this lesson, you will familiarize yourself with the basics of using K for
deductive program verification.

## 1. Setup: Simple Programming Language with Function Calls

We base this lesson on a simple programming language with functions,
assignment, if conditionals, and while loops. Take your time to study its
formalization below and save it in `procedures.k`:

```
module PROCEDURES-SYNTAX
    imports INT-SYNTAX
    imports BOOL-SYNTAX
    imports ID

    syntax Exp ::= IExp | BExp

    syntax IExp ::= Id | Int

    syntax KResult ::= Int | Bool | Ints

    // Take this sort structure:
    //
    //     IExp
    //    /    \
    // Int      Id
    //
    // Through the List{_, ","} functor.
    // Must add a `Bot`, for a common subsort for the empty list.

    syntax Bot
    syntax Bots ::= List{Bot, ","} [klabel(exps)]
    syntax Ints ::= List{Int, ","} [klabel(exps)]
                  | Bots
    syntax Ids  ::= List{Id, ","}  [klabel(exps)]
                  | Bots
    syntax Exps ::= List{Exp, ","} [klabel(exps), seqstrict]
                  | Ids | Ints

    syntax IExp ::= "(" IExp ")" [bracket]
                  | IExp "+" IExp [seqstrict]
                  | IExp "-" IExp [seqstrict]
                  > IExp "*" IExp [seqstrict]
                  | IExp "/" IExp [seqstrict]
                  > IExp "^" IExp [seqstrict]
                  | Id "(" Exps ")" [strict(2)]

    syntax BExp ::= Bool

    syntax BExp ::= "(" BExp ")" [bracket]
                  | IExp "<=" IExp [seqstrict]
                  | IExp "<"  IExp [seqstrict]
                  | IExp ">=" IExp [seqstrict]
                  | IExp ">"  IExp [seqstrict]
                  | IExp "==" IExp [seqstrict]
                  | IExp "!=" IExp [seqstrict]

    syntax BExp ::= BExp "&&" BExp
                  | BExp "||" BExp

    syntax Stmt ::=
         Id "=" IExp ";" [strict(2)]                        // Assignment
       | Stmt Stmt [left]                                   // Sequence
       | Block                                              // Block
       | "if" "(" BExp ")" Block "else" Block [strict(1)]   // If conditional
       | "while" "(" BExp ")" Block                         // While loop
       | "return" IExp ";"                    [seqstrict]   // Return statement
       | "def" Id "(" Ids ")" Block                         // Function definition

    syntax Block ::=
         "{" Stmt "}"    // Block with statement
       | "{" "}"         // Empty block
endmodule

module PROCEDURES
    imports INT
    imports BOOL
    imports LIST
    imports MAP
    imports PROCEDURES-SYNTAX

    configuration
      <k> $PGM:Stmt </k>
      <store> .Map </store>
      <funcs> .Map </funcs>
      <stack> .List </stack>

 // -----------------------------------------------
    rule <k> I1 + I2 => I1 +Int I2 ... </k>
    rule <k> I1 - I2 => I1 -Int I2 ... </k>
    rule <k> I1 * I2 => I1 *Int I2 ... </k>
    rule <k> I1 / I2 => I1 /Int I2 ... </k>
    rule <k> I1 ^ I2 => I1 ^Int I2 ... </k>

    rule <k> I:Id => STORE[I] ... </k>
         <store> STORE </store>

 // ------------------------------------------------
    rule <k> I1 <= I2 => I1  <=Int I2 ... </k>
    rule <k> I1  < I2 => I1   <Int I2 ... </k>
    rule <k> I1 >= I2 => I1  >=Int I2 ... </k>
    rule <k> I1  > I2 => I1   >Int I2 ... </k>
    rule <k> I1 == I2 => I1  ==Int I2 ... </k>
    rule <k> I1 != I2 => I1 =/=Int I2 ... </k>

    rule <k> B1 && B2 => B1 andBool B2 ... </k>
    rule <k> B1 || B2 => B1  orBool B2 ... </k>

    rule <k> S1:Stmt S2:Stmt => S1 ~> S2 ... </k>

    rule <k> ID = I:Int ; => . ... </k>
         <store> STORE => STORE [ ID <- I ] </store>

    rule <k> { S } => S ... </k>
    rule <k> {   } => . ... </k>

    rule <k> if (true)   THEN else _ELSE => THEN ... </k>
    rule <k> if (false) _THEN else  ELSE => ELSE ... </k>

    rule <k> while ( BE ) BODY => if ( BE ) { BODY while ( BE ) BODY } else { } ... </k>

    rule <k> def FNAME ( ARGS ) BODY => . ... </k>
         <funcs> FS => FS [ FNAME <- def FNAME ( ARGS ) BODY ] </funcs>

    rule <k> FNAME ( IS:Ints ) ~> CONT => #makeBindings(ARGS, IS) ~> BODY </k>
         <funcs> ... FNAME |-> def FNAME ( ARGS ) BODY ... </funcs>
         <store> STORE => .Map </store>
         <stack> .List => ListItem(state(CONT, STORE)) ... </stack>

    rule <k> return I:Int ; ~> _ => I ~> CONT </k>
         <stack> ListItem(state(CONT, STORE)) => .List ... </stack>
         <store> _ => STORE </store>

    rule <k> return I:Int ; ~> . => I </k>
         <stack> .List </stack>

    syntax KItem ::= #makeBindings(Ids, Ints)
                   | state(continuation: K, store: Map)
 // ----------------------------------------------------
    rule <k> #makeBindings(.Ids, .Ints) => . ... </k>
    rule <k> #makeBindings((I:Id, IDS => IDS), (IN:Int, INTS => INTS)) ... </k>
         <store> STORE => STORE [ I <- IN ] </store>
endmodule
```

Next, compile this example using `kompile procedures.k --backend haskell`. If
your processor is an Apple Silicon processor, add the `--no-haskell-binary`
flag if the compilation fails.

## 2. Setup: Proof Environment

Next, take the following snippet of K code and save it in `procedures-spec.k`.
This is a skeleton of the proof environment, and we will complete it as the
lesson progresses.

```
requires "procedures.k"
requires "domains.md"

module PROCEDURES-SPEC-SYNTAX
    imports PROCEDURES-SYNTAX

endmodule

module VERIFICATION
    imports K-EQUAL
    imports PROCEDURES-SPEC-SYNTAX
    imports PROCEDURES

endmodule

module PROCEDURES-SPEC
    imports VERIFICATION

endmodule
```

## 3. Claims

1. The first claim we will ask K to prove is that 3 + 4, in fact, equals 7.
   Claims are stated using the `claim` keyword, followed by the claim
   statement:

```
claim <k> 3 + 4 => 7 ... </k>
```

Add this claim to the `PROCEDURES-SPEC` module and run the K prover using the
command `kprove procedures-spec.k`. You should get back the output `#Top`,
which denotes the Matching Logic equivalent of `true` and means, in this
context, that all claims have been proven correctly.

2. The second claim reasons about the `if` statement that has a concrete condition:

```
claim <k> if ( 3 + 4 ==Int 7 ) {
            $a = 1 ;
            } else {
            $a = 2 ;
            }
        => . ... </k>
        <store> STORE => STORE [ $a <- 1 ] </store>
```

stating that the given program terminates (`=> .`), and when it does, the value
of the variable `$a` updated to `1`, meaning that the execution will have taken
the `then` branch. Add this claim to the `PROCEDURES-SPEC` module, but also add

```
syntax Id ::= "$a" [token]
```

to the `PROCEDURES-SPEC-SYNTAX` module in order to declare `$a` as a token so
that it can be used as a program variable. Re-run the K prover, which should
again return `#Top`.

3. Our third claim demonstrates how to reason about both branches of an `if`
   statement at the same time:

```
claim <k> $a = A:Int ; $b = B:Int ;
          if (A < B) {
            $c = B ;
          } else {
            $c = A ;
          }
        => . ... </k>
        <store> STORE => STORE [ $a <- A ] [ $b <- B ] [ $c <- ?C:Int ] </store>
    ensures (?C ==Int A) orBool (?C ==Int B)
```

The program in question first assigns symbolic integers `A` and `B` to program
variables `$a` and `$b`, respectively, and then executes the given `if`
statement, which has a symbolic condition (`A < B`), updating the value of the
program variable `$c` in both branches. The specification we give states that
the `if` statement terminates, with `$a` and `$b` updated, respectively, to `A`
and `B`, and `$c` updated to *some* symbolic integer value `?C`. Via the
`ensures` clause, which is used to specify additional constraints that hold
after execution, we also state that this existentially quantified `?C` equals
either `A` or `B`.

Add the productions declaring `$b` and `$c` as tokens to
`PROCEDURES-SPEC-SYNTAX` module, the claim to the `PROCEDURES-SPEC` module, run
the K prover again, and observe the output, which should not be `#Top` this
time. This means that K was not able to prove the claim, and we now need to
understand why. We do so by examining the output, which should look as follows:

```
    (InfoReachability) while checking the implication:
    The configuration's term unifies with the destination's term,
    but the implication check between the conditions has failed.

  #Not (
    #Exists ?C . {
        STORE [ $a <- A:Int ] [ $b <- B:Int ] [ $c <- ?C:Int ]
      #Equals
        STORE [ $a <- A:Int ] [ $b <- B:Int ] [ $c <- B:Int ]
    }
  #And
    {
      true
    #Equals
      ?C ==Int A orBool ?C ==Int B
    }
  )
#And
  <generatedTop>
    <k>
      _DotVar1
    </k>
    <store>
      STORE [ $a <- A:Int ] [ $b <- B:Int ] [ $c <- B:Int ]
    </store>
    <funcs>
      _Gen3
    </funcs>
    <stack>
      _Gen5
    </stack>
  </generatedTop>
#And
  {
    true
  #Equals
    A <Int B
  }
```

This output starts with a message telling us at which point the proof failed,
followed by the final state, which consists of three parts: some negative
Matching Logic (ML) constraints, the final configuration (`<generatedTop> ...
</generatedTop>`), and some positive ML constraints.

First, we examine the message:

```
(InfoReachability) while checking the implication:
The configuration's term unifies with the destination's term,
but the implication check between the conditions has failed.
```

which tells us that the *structure* of the final configuration is as expected,
but that some of the associated constraints cannot be proven. We next look at
the final configuration, in which the relevant item is the `<store> ...
</store>` cell, because it is the only one that we are reasoning about. By
inspecting its contents:

```
STORE [ $a <- A:Int ] [ $b <- B:Int ] [ $c <- B:Int ]
```

we see that we should be in the constraints of the `ensures`, since the value
of `$c` in the store equals `B` in this branch. We next examine the negative
and positive constraints of the output and, more often than not, the goal is to
instruct K how to use the information from the final configuration and the
positive constraints to falsify one of the negative constraints. This is done
through *simplifications*.

So, the positive constraint that we have is

```
{ true #Equals A <Int B }
```

meaning that `A <Int B` holds. Given the analysed program, this tells us that
we are in the `then` branch of the `if`. The negative constraint is

```
  #Not (
    #Exists ?C . {
        STORE [ $a <- A:Int ] [ $b <- B:Int ] [ $c <- ?C:Int ]
      #Equals
        STORE [ $a <- A:Int ] [ $b <- B:Int ] [ $c <- B:Int ]
    }
  #And
    { true #Equals ?C ==Int A orBool ?C ==Int B }
  )
```

and we observe, from the first equality, that the existential `?C` should be
instantiated with `B`. This would make both branches of the `#And` true,
falsifying the outside `#Not`. We just need to show `K` how to conclude that
`?C ==Int B`. We do so by introducing the following simplification into the
`VERIFICATION` module:

```
rule { M:Map [ K <- V ] #Equals M [ K <- V' ] } => { V #Equals V' } [simplification, anywhere]
```

which formalizes our internal understanding of why `?C ==Int B`, stating that
we update the same key in the same map with two values, and the resulting maps
are equal, then the two values must be equal as well. The `[simplification]`
attribute indicates to K to use this rule to simplify the state when trying to
prove claims. We will ignore the `anywhere` attribute for now. Re-run the K
prover, which should now return `#Top`, indicating that K was able to use the
simplification and prove the required claims.

4. Next, we show how to state and prove properties of `while` loops. In particular, we consider the following loop

```
claim
    <k>
        while ( 0 < $n ) {
            $s = $s + $n;
            $n = $n - 1;
            } => . ...
    </k>
    <store>
        $s |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2))
        $n |-> (N:Int => 0)
    </store>
    requires N >=Int 0
```

which adds the sum of first `$n` integers to `$s`, assuming the value of `$n`
is non-negative to begin with. This is reflected in the store by stating that,
after the execution of the loop, the original value of `$s` (which is set to
equal some symbolic integer `S`) is incremented by `((N +Int 1) *Int N /Int
2)`, and the value of `$n` always equals `0`. Add `$n` and `$s` as tokens in
the `PROCEDURES-SPEC-SYNTAX` module, the above claim to the `PROCEDURES-SPEC`
module, and run the K prover, which should return `#Top`.

5. Finally, our last claim is about a program that uses function calls:

```
claim
    <k>
        def $sum($n, .Ids) {
            $s = 0 ;
            while (0 < $n) {
                $s = $s + $n;
                $n = $n - 1;
            }
            return $s;
        }

        $s = $sum(N:Int, .Ints);
    => . ... </k>
    <funcs> .Map => ?_ </funcs>
    <store> $s |-> (_ => ((N +Int 1) *Int N /Int 2)) </store>
    <stack> .List </stack>
    requires N >=Int 0
```

Essentially, we have wrapped the `while` loop from claim 3.4 into a function
`$sum`, and then called that function with a symbolic integer `N`, storing the
return value in the variable `$s`. The specification states that this program
ends up storing the sum of first `N` integers in the variable `$n`. Add `$sum`
to the `PROCEDURES-SPEC-SYNTAX` module, the above claim to the
`PROCEDURES-SPEC` module, and run the K prover, which should again return
`#Top`.

## Exercises

1. Change the condition of the if statement in part 3.2 to take the `else`
   branch and adjust the claim so that the proof passes.

2. The post-condition of the specification in part 3.3 loses some information.
   In particular, the value of `?C` is in fact the maximum of `A` and `B`.
   Prove the same claim as in 3.2, but with the post-condition `ensures (?C
   ==Int maxInt(A, B))`.  For this, you will need to extend the `VERIFICATION`
   module with two simplifications that capture the meaning of `maxInt(A:Int,
   B:Int)`. Keep in mind that any rewriting rule can be used as a
   simplification; in particular, that simplifications can have `requires`
   clauses.

3. Following the pattern shown in part 3.4, assuming a non-negative initial
   value of `$b`, specify and verify the following `while` loop:

```
while ( 0 < $b ) {
    $a = $a + $c;
    $b = $b - 1;
    $c = $c - 1;
}
```

**Hint**: You will not need additional simplifications---once you've got the
specification right, the proof will go through.

4. Write an arbitrary yet not-too-complex function (or several functions
   interacting with each other), and try to specify and verify it (them) in K.
