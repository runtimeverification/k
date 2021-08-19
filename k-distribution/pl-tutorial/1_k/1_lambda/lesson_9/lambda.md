---
copyright: Copyright (c) 2014-2020 K Team. All Rights Reserved.
---

**K** code can be nested inside Markdown using annotated code blocks.
Use the tag `k` to tell the compiler which blocks to select.

Inside `.k` files, C/Java-like comments are available.
```k
// Single line comment
/* Multiline
comments */
```

Tutorial 1 --- LAMBDA
=====================

Author: Grigore Roșu (grosu@illinois.edu)  
Organization: University of Illinois at Urbana-Champaign

### Abstract
This file defines a simple functional language in **K**, called LAMBDA,
using a substitution style.  The explicit objective here is to teach some
**K** concepts and how they work in the K tool, and not to teach
λ-calculus or to argue for one definitional style against another
(e.g., some may prefer environment/closure-based definitions of such
languages).

Note that the subsequent definition is so simple, that it hardly shows any
of the strengths of **K**.  Perhaps the most interesting **K** aspect it shows is
that substitution can be defined fully generically, and then used to give
semantics to various constructs in various languages.

Note:
 **K** follows the
[literate programming](https://en.wikipedia.org/wiki/Literate_programming)
approach. The various semantic features defined in a **K**
module can be reordered at will and can be commented using normal
comments like in C/C++/Java.
While comments are useful in general, they can annoy the expert user
of **K**. To turn them off, you can do one of the following (unless you
want to remove them manually):  
(1) Use an [editor](https://github.com/kframework/k-editor-support) which can
hide or highlight Markdown and conventional C-like comments; or  
(2) Run `kompile --debug <def>`. Inside `./.kompiled-xxx/.md2.k/` you will find
all the K code extracted from the markdown files as used for compilation.

### Substitution
We need the predefined substitution module, so we require it with the command
below.  Then we should make sure we import its module called SUBSTITUTION
in our LAMBDA module below.

```k
require "substitution.md"

module LAMBDA-SYNTAX
  imports DOMAINS-SYNTAX
  imports KVAR-SYNTAX
```
### Basic Call-by-value λ-Calculus Syntax

We first define the syntax of conventional call-by-value λ-calculus, making
sure we declare the lambda abstraction construct to be a binder, the
lambda application to be strict, and the parentheses used for grouping as
a bracket.

Note:
Syntax in **K** is defined using the familiar BNF notation, with
terminals enclosed in quotes and nonterminals starting with capital
letters. **K** actually extends BNF with several attributes, which will be
described in this tutorial.

Note:
The `strict` constructs can evaluate their arguments in any (fully
interleaved) order.


The initial syntax of our λ-calculus:
```k
  syntax Val ::= KVar
               | "lambda" KVar "." Exp  [binder, latex(\lambda{#1}.{#2})]
  syntax Exp ::= Val
               | Exp Exp              [left, strict]
               | "(" Exp ")"          [bracket]
```

### Integer and Boolean Builtins Syntax
The LAMBDA arithmetic and Boolean expression constructs are simply rewritten
to their builtin counterparts once their arguments are evaluated.
The annotated operators in the right-hand side of the rules below are
builtin and come with the corresponding builtin sort. Note that the
variables appearing in these rules have integer sort. That means that these
rules will only be applied after the arguments of the arithmetic constructs
are fully evaluated to **K** results; this will happen thanks to their strictness
attributes declared as annotations to their syntax declarations (below).

```k
  syntax Val ::= Int | Bool
  syntax Exp ::= "-" Int
               > Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
```

### Conditional Syntax
Note that the `if` construct is strict only in its first argument.

```k
  syntax Exp ::= "if" Exp "then" Exp "else" Exp    [strict(1)]
```

### Let Binder
The let binder is a derived construct, because it can be defined using λ.

```k
  syntax Exp ::= "let" KVar "=" Exp "in" Exp
  rule let X = E in E':Exp => (lambda X . E') E                         [macro]
```

### Letrec Binder
We prefer a definition based on the μ construct.  Note that μ is not
really necessary, but it makes the definition of letrec easier to understand
and faster to execute.

```k
  syntax Exp ::= "letrec" KVar KVar "=" Exp "in" Exp
               | "mu" KVar "." Exp                  [binder, latex(\mu{#1}.{#2})]
  rule letrec F:KVar X:KVar = E in E' => let F = mu F . lambda X . E in E' [macro]
endmodule
```

### LAMBDA module

```k
module LAMBDA
  imports LAMBDA-SYNTAX
  imports SUBSTITUTION
  imports DOMAINS

  syntax KResult ::= Val
```

### β-reduction

```k
  rule (lambda X:KVar . E:Exp) V:Val => E[V / X]
```

### Integer Builtins

```k
  rule - I => 0 -Int I
  rule I1 * I2 => I1 *Int I2
  rule I1 / I2 => I1 /Int I2  requires I2 =/=Int 0
  rule I1 + I2 => I1 +Int I2
  rule I1 <= I2 => I1 <=Int I2
```

### Conditional

```k
  rule if true  then E else _ => E
  rule if false then _ else E => E
```

### Mu

```k
  rule mu X . E => E[(mu X . E) / X]
endmodule
```
