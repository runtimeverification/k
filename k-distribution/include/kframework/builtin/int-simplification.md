Integer Simplification
======================

This provides an attempt at a normal form for K integers.

```k
module INT-SIMPLIFICATION [symbolic, kore]
    imports INT
    imports BOOL
```

### Addition/Subtraction

```k
    rule A -Int A => 0 [simplification]
    rule A -Int 0 => A [simplification]
    rule 0 +Int A => A [simplification]
    rule A +Int 0 => A [simplification]

    rule  (A -Int  B) +Int B  => A [simplification]
    rule   A -Int (A  -Int B) => B [simplification]
    rule   A +Int (B  -Int A) => B [simplification]
    rule  (A +Int  B) -Int A  => B [simplification]

    rule  (A +Int B) +Int (C  -Int A) => B +Int C [simplification]
    rule  (A +Int B) -Int (A  +Int C) => B -Int C [simplification]
    rule  (A +Int B) -Int (C  +Int A) => B -Int C [simplification]
    rule  (A +Int B) +Int (C  -Int B) => A +Int C [simplification]
    rule ((A -Int B) -Int  C) +Int B  => A -Int C [simplification]

    rule   (A +Int  B  +Int C)  -Int (A  +Int D) =>  B +Int (C  -Int D) [simplification]
    rule   (C +Int (A  -Int D)) +Int (B  -Int A) =>  C +Int (B  -Int D) [simplification]
    rule (((A -Int  B) -Int C)  -Int  D) +Int B  => (A -Int  C) -Int D  [simplification]
```

We are attempting to move parenthesis to the left, and concrete terms to the right.

```k
    rule C1 +Int S2 => S2 +Int C1 [concrete(C1), symbolic(S2), simplification]

    rule S1 +Int (S2 +Int I3) => (S1 +Int S2) +Int I3 [symbolic(S1, S2), simplification]
    rule S1 +Int (S2 -Int I3) => (S1 +Int S2) -Int I3 [symbolic(S1, S2), simplification]
    rule S1 -Int (S2 +Int I3) => (S1 -Int S2) -Int I3 [symbolic(S1, S2), simplification]
    rule S1 -Int (S2 -Int I3) => (S1 -Int S2) +Int I3 [symbolic(S1, S2), simplification]

    rule S1 +Int (C2 -Int S3) => (S1 -Int S3) +Int C2 [symbolic(S1, S3), concrete(C2), simplification]
    rule S1 -Int (C2 -Int S3) => (S1 +Int S3) -Int C2 [symbolic(S1, S3), concrete(C2), simplification]

    rule (I1 +Int C2) +Int S3 => (I1 +Int S3) +Int C2 [concrete(C2), symbolic(S3), simplification]
    rule (I1 +Int C2) -Int S3 => (I1 -Int S3) +Int C2 [concrete(C2), symbolic(S3), simplification]
    rule (I1 -Int C2) +Int S3 => (I1 +Int S3) -Int C2 [concrete(C2), symbolic(S3), simplification]
    rule (I1 -Int C2) -Int S3 => (I1 -Int S3) -Int C2 [concrete(C2), symbolic(S3), simplification]

    rule (S1 +Int C2) +Int C3 => S1 +Int (C2 +Int C3) [concrete(C2, C3), symbolic(S1), simplification]
    rule (S1 +Int C2) -Int C3 => S1 +Int (C2 -Int C3) [concrete(C2, C3), symbolic(S1), simplification]
    rule (S1 -Int C2) +Int C3 => S1 +Int (C3 -Int C2) [concrete(C2, C3), symbolic(S1), simplification]
    rule (S1 -Int C2) -Int C3 => S1 -Int (C2 +Int C3) [concrete(C2, C3), symbolic(S1), simplification]
```

### Multiplication/Division

```k
    rule 1 *Int A => A [simplification]
    rule A *Int 1 => A [simplification]
    rule 0 *Int _ => 0 [simplification]
    rule _ *Int 0 => 0 [simplification]

    rule A /Int 1                   => A                            [simplification]
    rule (A *Int B) /Int A          => B        requires A =/=Int 0 [simplification]
    rule ((A *Int B) /Int C) /Int B => A /Int C requires B =/=Int 0 [simplification]
```

### Distributivity

```k
    rule (C *Int A) +Int (B *Int A)                      => (C +Int B) *Int A                        [simplification]
    rule (E *Int A) +Int B +Int C +Int D +Int (F *Int A) => ((E +Int F) *Int A) +Int B +Int C +Int D [simplification]
```

### Inequalities

```k
    rule I1 +Int C   <Int I2         => I1          <Int I2 -Int C  [concrete(C), simplification]
    rule C1          <Int I2 +Int C3 => C1 -Int C3  <Int I2         [concrete(C1, C3), simplification]
    rule C1         <=Int I2 +Int C3 => C1 -Int C3 <=Int I2         [concrete(C1, C3), simplification]

    rule A +Int B <Int A  => false requires 0 <=Int B [simplification]
    rule A <Int A -Int B  => false requires 0 <=Int B [simplification]
    rule 0 <Int 1 <<Int A => true  requires 0 <=Int A [simplification]

    rule          A  >Int B  => B  <Int A [simplification]
    rule          A >=Int B  => B <=Int A [simplification]
    rule notBool (A  <Int B) => B <=Int A [simplification]
    rule notBool (A <=Int B) => B  <Int A [simplification]

    rule 0                 <=Int A *Int B => true  requires 0 <=Int A andBool 0 <=Int B                                                      [simplification]
    rule A -Int B +Int C   <=Int D        => false requires D <Int A -Int B andBool 0 <=Int C                                                [simplification]
    rule (A *Int B) /Int C <=Int D        => true  requires 0 <=Int A andBool 0 <=Int B andBool 0 <Int C andBool A <=Int D andBool B <=Int C [simplification]
```

### Bitwise Operations

**TODO**: Should `A` be non-negative?

```k
    rule 0 |Int A => A [simplification]
    rule A |Int 0 => A [simplification]
    rule A |Int A => A [simplification]

    rule 0 &Int _ => 0 [simplification]
    rule _ &Int 0 => 0 [simplification]
    rule A &Int A => A [simplification]
```

### Modular Arithmetic

```k
    rule A modInt B => A requires 0 <=Int A andBool A <Int B [simplification]
```

### Minimum/Maximum

```k
    rule minInt(A, B) => A requires A <=Int B [simplification]

    rule minInt(A, B) <Int C  => true requires A  <Int C  orBool B  <Int C [simplification]
    rule A  <Int minInt(B, C) => true requires A  <Int B andBool A  <Int C [simplification]
    rule A <=Int minInt(B, C) => true requires A <=Int B andBool A <=Int C [simplification]

    rule A <=Int maxInt(B, C) => true requires A <=Int B orBool A <=Int C [simplification]
```

```k
endmodule
```
