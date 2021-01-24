module FUN-TEST
  imports INT
  imports STRING
  imports MAP

  configuration
    <k> $PGM:KItem </k>
    <cell> .Map </cell>

syntax KItem ::= nestedFun( Int )
rule nestedFun(A) => #fun(B => #fun(C => 100 *Int A +Int 10 *Int B +Int C)(2 *Int B))(2 *Int A)

syntax KItem ::= nestedFunString ( Int )
rule nestedFunString(A) => #fun(B => #fun(C => Int2String(A) +String Int2String(B) +String Int2String(C))(2 *Int B))(2 *Int A)

syntax FooT ::= "#foo"
syntax BarT ::= "#bar"

syntax BarT ::= fooToBar( FooT )
rule fooToBar( #foo ) => #bar

syntax KItem ::= useFooToBar( FooT )
rule useFooToBar(FOO) => #fun(F => fooToBar(F))(FOO)

syntax KItem ::= useNestedFooToBar( FooT )
rule useNestedFooToBar(FOO) => #fun(F2 => #fun(F3 => fooToBar(F3))(F2) )(FOO)

syntax FooInt ::= Int
syntax FooInt ::= getFooInt() [function]
rule getFooInt() => 0

syntax BarInt ::= Int
syntax BarInt ::= getBarInt() [function]
rule getBarInt() => 1

syntax KItem ::= useFooBarInt()
rule useFooBarInt() => #fun( _FOO => getBarInt() )(getFooInt())

// LLVM error
syntax KItem ::= useNestedBarInt()
rule useNestedBarInt()
     => #fun(_FOO
          => #fun(_F2 => getBarInt() )(0)
        )(0)

  syntax KItem ::= nestedFun3Levels()
  rule nestedFun3Levels()
       => #fun(V1
       => #fun(_V2
       => #fun(_V3
       => requiresConfig()
          )(V1 *Int 0)
          )(0)
          )(0)

  syntax Int ::= requiresConfig() [function]
  rule [[ requiresConfig() => 0 ]]
    <cell> _M </cell>

  syntax IntList ::= List{Int, ""}

  syntax KItem ::= callFunIntListAndConfig()
  rule callFunIntListAndConfig() => funIntListAndConfig()

  syntax Int ::= funIntListAndConfig()     [function]
  rule [[ funIntListAndConfig() => #fun(_V1 => 0)(.IntList) ]]
    <cell> _M </cell>

  syntax KItem ::= Int
  syntax Int ::= funSortTest(Int) [function]
  rule funSortTest(I)
    => #fun(BALANCE
    => #fun(ROOT
    => BALANCE +Int ROOT)(I))(I)

  syntax KItem ::= Hash
  syntax Hash ::= funSortTest2() [function]
  rule funSortTest2()
    => #fun(EPOCH
    => #fun(CommitteesPerSlot
    => #fun(OFFSET
    => #fun(SHARD
    => #fun(FirstCommittee
    => #fun(MaxRandomByte
    => #fun(SEED
    => #fun(I
    => funSortTest2Aux(EPOCH, CommitteesPerSlot, OFFSET, SHARD, FirstCommittee, MaxRandomByte, SEED, I)
       )(0)
       )(get_seed(EPOCH))
       )(0)
       )(0)
       )(0)
       )(0)
       )(0)
       )(0)

  syntax Hash ::= funSortTest2Aux(Int, Int, Int, Int, Int, Int, h: Hash, Int) [function]
  rule funSortTest2Aux(... h: H) => H

  syntax Hash ::= "foo"
  syntax Hash ::= "get_seed" "(" Int ")" [function]
  rule get_seed(_) => foo

endmodule
