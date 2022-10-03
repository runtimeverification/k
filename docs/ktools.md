K Tools
=======

Here we document how to use some of the most commonly used K tools.

Debugging
---------

The LLVM Backend has support for integration with GDB. You can run the debugger
on a particular program by passing the `--debugger` flag to krun, or by
invoking the llvm backend interpreter directly. Below we provide a simple
tutorial to explain some of the basic commands supported by the LLVM backend.

### LLDB Support

GDB is not well-supported on macOS, particularly on newer OS versions and Apple
Silicon ARM hardware. Consequently, if the `--debugger` option is passed to krun
on macOS, LLDB[^1] is launched instead of GDB. However, the K-specific debugger
scripts that GDB uses have not been ported to LLDB yet, and so the instructions
in the rest of this section will not work.

### The K Definition

Here is a sample K definition we will use to demonstrate debugging
capabilities:

```k
module TEST
  imports INT

  configuration <k> foo(5) </k>
  rule [test]: I:Int => I +Int 1 requires I <Int 10

  syntax Int ::= foo(Int) [function]
  rule foo(I) => 0 -Int I

endmodule
```

You should compile this definition with `--backend llvm -ccopt -g` and without
`-ccopt -O2` in order to use the debugger most effectively.

### Stepping

**Important:** When you first run `krun` with option `--debugger`, GDB will
instruct you on how to modify ~/.gdbinit to enable printing abstract syntax
of K terms in the debugger. If you do not perform this step, you can still
use all the other features, but K terms will be printed as their raw address
in memory. GDB will need the kompiled interpreter in its safe path in order
to access the pretty printing python script within it. A good way to do this
would be to pick a minimum top-level path that covers all of your kompiled
semantics (ie. `set auto-load safe-path ~/k-semantics`)

You can break before every step of execution is taken by setting a breakpoint
on the `step` function:

```
(gdb) break definition.kore:step
Breakpoint 1 at 0x25e340
(gdb) run
Breakpoint 1, 0x000000000025e340 in step (subject=`<generatedTop>{}`(`<k>{}`(`kseq{}`(`inj{Int{}, KItem{}}`(#token("0", "Int")),dotk{}(.KList))),`<generatedCounter>{}`(#token("0", "Int"))))
(gdb) continue
Continuing.

Breakpoint 1, 0x000000000025e340 in step (subject=`<generatedTop>{}`(`<k>{}`(`kseq{}`(`inj{Int{}, KItem{}}`(#token("1", "Int")),dotk{}(.KList))),`<generatedCounter>{}`(#token("0", "Int"))))
(gdb) continue 2
Will ignore next crossing of breakpoint 1.  Continuing.

Breakpoint 1, 0x000000000025e340 in step (subject=`<generatedTop>{}`(`<k>{}`(`kseq{}`(`inj{Int{}, KItem{}}`(#token("3", "Int")),dotk{}(.KList))),`<generatedCounter>{}`(#token("0", "Int"))))
(gdb)
```

### Breaking on a specific rule

You can break when a rule is applied by giving the rule a rule label. If the
module name is TEST and the rule label is test, you can break when the rule
applies by setting a breakpoint on the `TEST.test.rhs` function:

```
(gdb) break TEST.test.rhs
Breakpoint 1 at 0x25e250: file /home/dwightguth/test/./test.k, line 4.
(gdb) run
Breakpoint 1, TEST.test.rhs (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList), VarI=#token("0", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb)
```

Note that the substitution associated with that rule is visible in the
description of the frame.

You can also break when a side condition is applied using the `TEST.test.sc`
function:

```
(gdb) break TEST.test.sc
Breakpoint 1 at 0x25e230: file /home/dwightguth/test/./test.k, line 4.
(gdb) run
Breakpoint 1, TEST.test.sc (VarI=#token("0", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb)
```

Note that every variable used in the side condition can have its value
inspected when stopped at this breakpoint, but other variables are not visible.

You can also break on a rule by its location:

```
(gdb) break test.k:4
Breakpoint 1 at 0x25e230: test.k:4. (2 locations)
(gdb) run
Breakpoint 1, TEST.test.sc (VarI=#token("0", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb) continue
Continuing.

Breakpoint 1, TEST.test.rhs (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList), VarI=#token("0", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb) continue
Continuing.

Breakpoint 1, TEST.test.sc (VarI=#token("1", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb)
```

Note that this sets a breakpoint at two locations: one on the side condition
and one on the right hand side. If the rule had no side condition, the first
would not be set. You can also view the locations of the breakpoints and
disable them individually:

```
(gdb) info breakpoint
Num     Type           Disp Enb Address            What
1       breakpoint     keep y   <MULTIPLE>
        breakpoint already hit 3 times
1.1                         y     0x000000000025e230 in TEST.test.sc at /home/dwightguth/test/./test.k:4
1.2                         y     0x000000000025e250 in TEST.test.rhs at /home/dwightguth/test/./test.k:4
(gdb) disable 1.1
(gdb) continue
Continuing.

Breakpoint 1, TEST.test.rhs (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList), VarI=#token("1", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb) continue
Continuing.

Breakpoint 1, TEST.test.rhs (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList), VarI=#token("2", "Int")) at /home/dwightguth/test/./test.k:4
4         rule [test]: I:Int => I +Int 1 requires I <Int 10
(gdb)
```

Now only the breakpoint when the rule applies is enabled.

### Breaking on a function

You can also break when a particular function in your semantics is invoked:

```
(gdb) info functions foo
All functions matching regular expression "foo":

File /home/dwightguth/test/./test.k:
struct __mpz_struct *Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int(struct __mpz_struct *);
(gdb) break Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int
Breakpoint 1 at 0x25e640: file /home/dwightguth/test/./test.k, line 6.
(gdb) run
Breakpoint 1, Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int (_1=#token("1", "Int")) at /home/dwightguth/test/./test.k:6
6         syntax Int ::= foo(Int) [function]
(gdb)
```

In this case, the variables have numbers instead of names because the names of
arguments in functions in K come from rules, and we are stopped before any
specific rule has applied. For example, `_1` is the first argument to the
function.

You can also set a breakpoint in this location by setting it on the line
associated with its production:

```
(gdb) break test.k:6
Breakpoint 1 at 0x25e640: file /home/dwightguth/test/./test.k, line 6.
(gdb) run
Breakpoint 1, Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int (_1=#token("1", "Int")) at /home/dwightguth/test/./test.k:6
6         syntax Int ::= foo(Int) [function]
```

These two syntaxes are equivalent; use whichever is easier for you.

You can also view the stack of function applications:

```
(gdb) bt
#0  Lblfoo'LParUndsRParUnds'TEST'UndsUnds'Int (_1=#token("1", "Int")) at /home/dwightguth/test/./test.k:6
#1  0x000000000025e5f8 in apply_rule_111 (VarDotVar0=`<generatedCounter>{}`(#token("0", "Int")), VarDotVar1=dotk{}(.KList)) at /home/dwightguth/test/./test.k:9
#2  0x0000000000268a52 in take_steps ()
#3  0x000000000026b7b4 in main ()
(gdb)
```

Here we see that `foo` was invoked while applying the rule on line 9 of test.k,
and we also can see the substitution of that rule. If foo was evaluated while
evaluating another function, we would also be able to see the arguments of that
function as well, unless the function was tail recursive, in which case no
stack frame would exist once the tail call was performed.

### Breaking on a set of rules or functions

Using `rbreak <regex>` you can set breakpoints on multiple functions.

-   `rbreak Lbl` - sets a breakpoint on all non hooked `function`s

-   `rbreak Lbl.*TEST` - sets a breakpoint on all `function`s from module `TEST`

-   `rbreak hook_INT` - sets a breakpoint on all hooks from module `INT`

### Other debugger issues

-   `<optimized out>` try kompiling without `-O1`, `-O2`, or `-O3`.
-   `(gdb) break definition.kore:break -> No source file named definition.kore.`
send `-ccopt -g` to kompile in order to generate debug info symbols.

Profiling your K semantics
--------------------------

The first thing to be aware of is in order to get meaningful data,
you need to build the semantics and all of its dependencies with
optimizations enabled but _without the frame pointer elimination
optimization_. For example, for EVM, this means rebuilding GMP, MPFR,
JEMalloc, Crypto++, SECP256K1, etc with the following `exports`.

```sh
export CFLAGS="-DNDEBUG -O2 -fno-omit-frame-pointer"
export CXXFLAGS="-DNDEBUG -O2 -fno-omit-frame-pointer"
```

You can skip this step, but if you do, any samples within these
libraries will not have correct stack trace information, which means
you will likely not get a meaningful set of data that will tell you
where the majority of time is really being spent. Don't worry about
rebuilding literally every single dependency though. Just focus on the
ones that you expect to take a non-negligible amount of runtime. You
will be able to tell if you haven't done enough later, and you can go
back and rebuild more.  Once this is done, you then build K with
optimizations and debug info enabled, like so:

```sh
mvn package -Dproject.build.type="FastBuild"
```

Next, you build the semantics with optimizations and debug info
enabled (i.e., `kompile -ccopt -O2 --iterated -ccopt -fno-omit-frame-pointer`).

Once all this is done, you should be ready to profile your
application. Essentially, you should run whatever test suite you
usually run, but with `perf record -g -- ` prefixed to the front. For
example, for KEVM it's the following command. (For best data, don't
run this step in parallel.)

```sh
perf record -g -- make test-conformance
```

Finally, you want to filter out just the samples that landed within
the llvm backend and view the report. For this, you need to know the
name of the binary that was generated by your build system. Normally
it is `interpreter`, but e.g. if you are building the web3 client for
kevm, it would be `kevm-client`. You will want to run the following
command.

```sh
perf report -g -c $binary_name
```

If all goes well, you should see a breakdown of where CPU time has
been spent executing the application. You will know that sufficient
time was spent rebuilding dependencies with the correct flags when the
total time reported by the main method is close to 100%. If it's not
close to 100%, this is probably because a decent amount of self time
was reported in stack traces that were not built with frame pointers
enabled, meaning that perf was unable to walk the stack. You will have
to go back, rebuild the appropriate libraries, and then record your
trace again.

Your ultimate goal is to identify the hotspots that take the most
time, and make them execute faster. Entries like `step` and
`step_1234` like functions refer to the cost of matching. An entry
like `side_condition_1234` is a side condition and `apply_rule_1234`
is constructing the rhs of a rule. You can convert from this rule
ordinal to a location using the `llvm-kompile-compute-loc` script in
the bin folder of the llvm backend repo. For example,

```sh
llvm-kompile-compute-loc 5868 evm-semantics/.build/defn/llvm/driver-kompiled
```

spits out the following text.

```
Line: 18529
/home/dwightguth/evm-semantics/./.build/defn/llvm/driver.k:493:10
```

This is the line of `definition.kore` that the axiom appears on as
well as the original location of the rule in the K semantics. You can
use this information to figure out which rules and functions are
causing the most time and optimize them to be more efficient.
