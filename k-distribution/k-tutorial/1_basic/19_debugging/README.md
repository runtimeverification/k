---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

# Lesson 1.19: Debugging with GDB or LLDB

The purpose of this lesson is to teach how to debug your K interpreter using
the K-language support provided in [GDB](https://www.gnu.org/software/gdb/) or
[LLDB](https://lldb.llvm.org/index.html).

## Caveats

This lesson has been written with GDB support on Linux in mind. Unfortunately,
on macOS, GDB has limited support. To address this, we have introduced early
experimental support for debugging with LLDB on macOS. In some cases, the
features supported by LLDB are slightly different to those supported by GDB; the
tutorial text will make this clear where necessary. If you use a macOS with an
LLVM version older than 15, you may need to upgrade it to use the LLDB
correctly. If you encounter an issue on either operating system, please open an
issue against the [K repository](https://github.com/runtimeverification/k).

## Getting started

On Linux, you will need GDB in order to complete this lesson. If you do not
already have GDB installed, then do so. Steps to install GDB are outlined in
this [GDB Tutorial](http://www.gdbtutorial.com/tutorial/how-install-gdb).

On macOS, LLDB should already have been installed with K's build dependencies
(whether you have built K from source, or installed it using `kup` or Homebrew).

The first thing neccessary in order to debug a K interpreter is to build the
interpreter with full debugging support enabled. This can be done relatively
simply. First, run `kompile` with the command line flag `--enable-llvm-debug`.
The resulting compiled K definition will be ready to support debugging.

Once you have a compiled K definition and a program you wish to debug, you can
start the debugger by passing the `--debugger` flag to `krun`. This will
automatically load the program you are executing into GDB and drop you into a
GDB shell ready to start executing the program.

As an example, consider the following K definition (`lesson-19-a.k`):

```k
module LESSON-19-A
  imports INT

  rule I => I +Int 1
    requires I <Int 100
endmodule
```

If we compile this definition with `kompile lesson-19-a.k --enable-llvm-debug`,
and run the program `0` in the debugger with `krun -cPGM=0 --debugger`, we will
see the following output (roughly, and depending on which platform you are
using):

### GDB / Linux

```
GNU gdb (Ubuntu 9.2-0ubuntu1~20.04) 9.2
Copyright (C) 2020 Free Software Foundation, Inc.
License GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.
Type "show copying" and "show warranty" for details.
This GDB was configured as "x86_64-linux-gnu".
Type "show configuration" for configuration details.
For bug reporting instructions, please see:
<http://www.gnu.org/software/gdb/bugs/>.
Find the GDB manual and other documentation resources online at:
    <http://www.gnu.org/software/gdb/documentation/>.

For help, type "help".
Type "apropos word" to search for commands related to "word"...
Reading symbols from ./lesson-19-a-kompiled/interpreter...
warning: File "/home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-a-kompiled/interpreter" auto-loading has been declined by your `auto-load safe-path' set to "$debugdir:$datadir/auto-load".
To enable execution of this file add
        add-auto-load-safe-path /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-a-kompiled/interpreter
line to your configuration file "/home/dwightguth/.gdbinit".
To completely disable this security protection add
        set auto-load safe-path /
line to your configuration file "/home/dwightguth/.gdbinit".
For more information about this security protection see the
"Auto-loading safe path" section in the GDB manual.  E.g., run from the shell:
        info "(gdb)Auto-loading safe path"
(gdb)
```

To make full advantage of the GDB features of K, you should follow the first
command listed in this output message and add the corresponding
`add-auto-load-safe-path` command to your `~/.gdbinit` file as prompted.
Please note that the path will be different on your machine than the one
listed above. Adding directories to the "load safe path" effectively tells GDB
to trust those directories. All content under a given directory will be recursively
trusted, so if you want to avoid having to add paths to the "load safe path" every
time you kompile a different `K` definition, then you can just trust a minimal
directory containing all your kompiled files; however, do not choose a top-level directory containing arbitrary files as this amounts to trusting arbitrary files and is a security risk. More info on the load safe path
can be found [here](https://sourceware.org/gdb/onlinedocs/gdb/Auto_002dloading-safe-path.html).

### LLDB / macOS

```
(lldb) target create "./lesson-19-a-kompiled/interpreter"
warning: 'interpreter' contains a debug script. To run this script in this debug session:

    command script import "/Users/brucecollie/code/scratch/lesson-19-a-kompiled/interpreter.dSYM/Contents/Resources/Python/interpreter.py"

To run all discovered debug scripts in this session:

    settings set target.load-script-from-symbol-file true

Current executable set to '/Users/brucecollie/code/scratch/lesson-19-a-kompiled/interpreter' (x86_64).
(lldb) settings set -- target.run-args  ".krun-2023-03-20-11-22-46-TcYt9ffhb2/tmp.in.RupiLwHNfn" "-1" ".krun-2023-03-20-11-22-46-TcYt9ffhb2/result.kore"
(lldb) 
```

LLDB applies slightly different security policies to GDB. To load K's debugging
scripts for this session only, you can run the `command script import` line at
the LLDB prompt. The loaded scripts will not persist across debugging sessions
if you do this. It is also possible to configure LLDB to automatically load the
K scripts when an interpreter is started in LLDB; doing so requires a slightly
less broad permission than GDB.

On macOS, the `.dSYM` directory that contains debugging symbols for an
executable can also contain Python scripts in `Contents/Resources/Python`. If
there is a Python script with a name matching the name of the current executable
(here, `interpreter` and `interpreter.py`), it will be automatically loaded if
the `target.load-script-from-symbol-file` setting is set). You can therefore add
the `settings set` command to your `~/.lldbinit` without enabling full arbitrary
code execution, but you should be aware of the paths from which code _can_ be
executed if you do so.

## Basic commands

> **LLDB Note:** the `k start` and `k step` commands are currently not
> implemented in the K LLDB scripts. To work around this limitation temporarily,
> you can run `process launch --stop-at-entry` instead of `k start`. To emulate
> `k step`, first run `rbreak k_step` once, then `continue` instead of each `k
> step`. We hope to address these limitations soon.

The most basic commands you can execute in the K GDB session are to run your
program or to step through it. The first can be accomplished using GDB's
built-in `run` command. This will automatically start the program and begin
executing it. It will continue until the program aborts or finishes, or the
debugger is interrupted with Ctrl-C.

Sometimes you want finer-grained control over how you proceed through the
program you are debugging. To step through the rule applications in your
program, you can use the `k start` and `k step` GDB commands.

`k start` is similar to the built-in `start` command in that it starts the
program and then immediately breaks before doing any work. However, unlike
the `start` command which will break immediately after the `main` method of
a program is executed, the `K start` program will initialize the rewriter,
evaluate the initial configuration, and break immediately prior to applying
any rewrite steps.

In the example above, here is what we see when we run the `k start` command:

```
Temporary breakpoint 1 at 0x239210
Starting program: /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-a-kompiled/interpreter .krun-2021-08-13-14-10-50-sMwBkbRicw/tmp.in.01aQt85TaA -1 .krun-2021-08-13-14-10-50-sMwBkbRicw/result.kore
[Thread debugging using libthread_db enabled]
Using host libthread_db library "/lib/x86_64-linux-gnu/libthread_db.so.1".

Temporary breakpoint 1, 0x0000000000239210 in main ()
0x0000000000231890 in step (subject=<k>
  0 ~> .
</k>)
(gdb)
```

As you can see, we are stopped at the `step` function in the interpreter.
This function is responsible for taking top-level rewrite steps. The `subject`
parameter to this function is the current K configuration.

We can step through K rewrite steps one at a time by running the `k step`
command. By default, this takes a single rewrite step (including any function
rule applications that are part of that step).

Here is what we see when we run that command:

```
Continuing.

Temporary breakpoint -22, 0x0000000000231890 in step (subject=<k>
  1 ~> .
</k>)
(gdb)
```

As we can see, we have taken a single rewrite step. We can also pass a number
to the `k step` command which indicates the number of rewrite steps to take.

Here is what we see if we run `k step 10`:

```
Continuing.

Temporary breakpoint -23, 0x0000000000231890 in step (subject=<k>
  11 ~> .
</k>)
(gdb)
```

As we can see, ten rewrite steps were taken.

## Breakpoints

The next important step in debugging an application in GDB is to be able to
set breakpoints. Generally speaking, there are three types of breakpoints we
are interested in a K semantics: Setting a breakpoint when a particular
function is called, setting a breakpoint when a particular rule is applied,
and setting a breakpoint when a side condition of a rule is evaluated.

The easiest way to do the first two things is to set a breakpoint on the
line of code containing the function or rule.

For example, consider the following K definition (`lesson-19-b.k`):

```k
module LESSON-19-B
  imports BOOL

  syntax Bool ::= isBlue(Fruit) [function]
  syntax Fruit ::= Blueberry() | Banana()
  rule isBlue(Blueberry()) => true
  rule isBlue(Banana()) => false

  rule F:Fruit => isBlue(F)
endmodule
```

Once this program has been compiled for debugging, we can run the program
`Blueberry()`. We can then set a breakpoint that stops when the `isBlue`
function is called with the following command in GDB:
```
break lesson-19-b.k:4
```

Similarly, in LLDB, run:
```
breakpoint set --file lesson-19-b.k --line 4
```

Here is what we see if we set this breakpoint and then run the interpreter:

```
(gdb) break lesson-19-b.k:4
Breakpoint 1 at 0x231040: file /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-b.k, line 4.
(gdb) run
Starting program: /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-b-kompiled/interpreter .krun-2021-08-13-14-20-27-vXOQmV6lwS/tmp.in.fga98yqXlc -1 .krun-2021-08-13-14-20-27-vXOQmV6lwS/result.kore
[Thread debugging using libthread_db enabled]
Using host libthread_db library "/lib/x86_64-linux-gnu/libthread_db.so.1".

Breakpoint 1, LblisBlue'LParUndsRParUnds'LESSON-19-B'Unds'Bool'Unds'Fruit (_1=Blueberry ( )) at /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-b.k:4
4         syntax Bool ::= isBlue(Fruit) [function]
(gdb)
```

```
(lldb) breakpoint set --file lesson-19-b.k --line 4
Breakpoint 1: where = interpreter`LblisBlue'LParUndsRParUnds'LESSON-19-B'Unds'Bool'Unds'Fruit + 20 at lesson-19-b.k:4:19, address = 0x0000000100003ff4
(lldb) run
Process 50546 launched: '/Users/brucecollie/code/scratch/lesson-19-b-kompiled/interpreter' (x86_64)
Process 50546 stopped
* thread #1, queue = 'com.apple.main-thread', stop reason = breakpoint 1.1
    frame #0: 0x0000000100003ff4 interpreter`LblisBlue'LParUndsRParUnds'LESSON-19-B'Unds'Bool'Unds'Fruit(_1=Blueberry ( )) at lesson-19-b.k:4:19
   1   	module LESSON-19-B
   2   	  imports BOOL
   3   	
-> 4   	  syntax Bool ::= isBlue(Fruit) [function]
   5   	  syntax Fruit ::= Blueberry() | Banana()
   6   	  rule isBlue(Blueberry()) => true
   7   	  rule isBlue(Banana()) => false
(lldb)
```

As we can see, we have stopped at the point where we are evaluating that
function. The value `_1` that is a parameter to that function shows the
value passed to the function by the caller.

We can also break when the `isBlue(Blueberry()) => true` rule applies by simply
changing the line number to the line number of that rule:

```
(gdb) break lesson-19-b.k:6
Breakpoint 1 at 0x2af710: file /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-b.k, line 6.
(gdb) run
Starting program: /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-b-kompiled/interpreter .krun-2021-08-13-14-32-36-7kD0ic7XwD/tmp.in.8JNH5Qtmow -1 .krun-2021-08-13-14-32-36-7kD0ic7XwD/result.kore
[Thread debugging using libthread_db enabled]
Using host libthread_db library "/lib/x86_64-linux-gnu/libthread_db.so.1".

Breakpoint 1, apply_rule_138 () at /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-b.k:6
6         rule isBlue(Blueberry()) => true
(gdb)
```

```
(lldb) breakpoint set --file lesson-19-b.k --line 6
Breakpoint 1: where = interpreter`apply_rule_140 at lesson-19-b.k:6:8, address = 0x0000000100004620
(lldb) run
Process 50681 launched: '/Users/brucecollie/code/scratch/lesson-19-b-kompiled/interpreter' (x86_64)
Process 50681 stopped
* thread #1, queue = 'com.apple.main-thread', stop reason = breakpoint 1.1
    frame #0: 0x0000000100004620 interpreter`apply_rule_140 at lesson-19-b.k:6:8
   3   	
   4   	  syntax Bool ::= isBlue(Fruit) [function]
   5   	  syntax Fruit ::= Blueberry() | Banana()
-> 6   	  rule isBlue(Blueberry()) => true
   7   	  rule isBlue(Banana()) => false
   8   	
   9   	  rule F:Fruit => isBlue(F)
(lldb) 
```

We can also do the same with a top-level rule:

```
(gdb) break lesson-19-b.k:9
Breakpoint 1 at 0x2aefa0: lesson-19-b.k:9. (2 locations)
(gdb) run
Starting program: /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-b-kompiled/interpreter .krun-2021-08-13-14-33-13-9fC8Sz4aO3/tmp.in.jih1vtxSiQ -1 .krun-2021-08-13-14-33-13-9fC8Sz4aO3/result.kore
[Thread debugging using libthread_db enabled]
Using host libthread_db library "/lib/x86_64-linux-gnu/libthread_db.so.1".

Breakpoint 1, apply_rule_107 (Var'Unds'DotVar0=<generatedCounter>
  0
</generatedCounter>, Var'Unds'DotVar1=., VarF=Blueberry ( )) at /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-b.k:9
9         rule F:Fruit => isBlue(F)
(gdb)
```

```
(lldb) breakpoint set --file lesson-19-b.k --line 9
Breakpoint 1: 2 locations.
(lldb) run
Process 50798 launched: '/Users/brucecollie/code/scratch/lesson-19-b-kompiled/interpreter' (x86_64)
Process 50798 stopped
* thread #1, queue = 'com.apple.main-thread', stop reason = breakpoint 1.1
    frame #0: 0x0000000100003f2e interpreter`apply_rule_109(Var'Unds'DotVar0=<generatedCounter>
  0
</generatedCounter>, Var'Unds'DotVar1=., VarF=Blueberry ( )) at lesson-19-b.k:9:8
   6   	  rule isBlue(Blueberry()) => true
   7   	  rule isBlue(Banana()) => false
   8   	
-> 9   	  rule F:Fruit => isBlue(F)
   10  	endmodule
(lldb)  
```

Unlike the function rule above, we see several parameters to this function.
These are the substitution that was matched for the function. Variables only
appear in this substitution if they are actually used on the right-hand side
of the rule.

## Advanced breakpoints

Sometimes it is inconvenient to set the breakpoint based on a line number.

It is also possible to set a breakpoint based on the rule label of a particular
rule. Consider the following definition (`lesson-19-c.k`):

```k
module LESSON-19-C
  imports INT
  imports BOOL

  syntax Bool ::= isEven(Int) [function]
  rule [isEven]: isEven(I) => true requires I %Int 2 ==Int 0
  rule [isOdd]: isEven(I) => false requires I %Int 2 =/=Int 0

endmodule
```

We will run the program `isEven(4)`. We can set a breakpoint for when a rule
applies by means of the `MODULE-NAME.label.rhs` syntax:

```
(gdb) break LESSON-19-C.isEven.rhs
Breakpoint 1 at 0x2afda0: file /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-c.k, line 6.
(gdb) run
Starting program: /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-c-kompiled/interpreter .krun-2021-08-13-14-40-29-LNNT8YEZ61/tmp.in.ZG93vWCGGC -1 .krun-2021-08-13-14-40-29-LNNT8YEZ61/result.kore
[Thread debugging using libthread_db enabled]
Using host libthread_db library "/lib/x86_64-linux-gnu/libthread_db.so.1".

Breakpoint 1, LESSON-19-C.isEven.rhs () at /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-c.k:6
6         rule [isEven]: isEven(I) => true requires I %Int 2 ==Int 0
(gdb)
```

```
(lldb) breakpoint set --name LESSON-19-C.isEven.rhs
Breakpoint 1: where = interpreter`LESSON-19-C.isEven.rhs at lesson-19-c.k:6:18, address = 0x00000001000038e0
(lldb) run
Process 51205 launched: '/Users/brucecollie/code/scratch/lesson-19-c-kompiled/interpreter' (x86_64)
Process 51205 stopped
* thread #1, queue = 'com.apple.main-thread', stop reason = breakpoint 1.1
    frame #0: 0x00000001000038e0 interpreter`LESSON-19-C.isEven.rhs at lesson-19-c.k:6:18
   3   	  imports BOOL
   4   	
   5   	  syntax Bool ::= isEven(Int) [function]
-> 6   	  rule [isEven]: isEven(I) => true requires I %Int 2 ==Int 0
   7   	  rule [isOdd]: isEven(I) => false requires I %Int 2 =/=Int 0
   8   	
   9   	endmodule
(lldb) 
```

We can also set a breakpoint for when a rule's side condition is evaluated
by means of the `MODULE-NAME.label.sc` syntax:

```
(gdb) break LESSON-19-C.isEven.sc
Breakpoint 1 at 0x2afd70: file /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-c.k, line 6.
(gdb) run
Starting program: /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-c-kompiled/interpreter .krun-2021-08-13-14-41-48-1BoGfJRbYc/tmp.in.kg4F8cwfCe -1 .krun-2021-08-13-14-41-48-1BoGfJRbYc/result.kore
[Thread debugging using libthread_db enabled]
Using host libthread_db library "/lib/x86_64-linux-gnu/libthread_db.so.1".

Breakpoint 1, LESSON-19-C.isEven.sc (VarI=4) at /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-c.k:6
6         rule [isEven]: isEven(I) => true requires I %Int 2 ==Int 0
(gdb) finish
Run till exit from #0  LESSON-19-C.isEven.sc (VarI=4) at /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-c.k:6
0x00000000002b2662 in LblisEven'LParUndsRParUnds'LESSON-19-C'Unds'Bool'Unds'Int (_1=4) at /home/dwightguth/kframework-5.0.0/k-distribution/k-tutorial/1_basic/19_debugging/lesson-19-c.k:5
5         syntax Bool ::= isEven(Int) [function]
Value returned is $1 = true
(gdb)
```

```
(lldb) breakpoint set --name LESSON-19-C.isEven.sc
Breakpoint 1: where = interpreter`LESSON-19-C.isEven.sc + 1 at lesson-19-c.k:6:18, address = 0x00000001000038c1
(lldb) run
Process 52530 launched: '/Users/brucecollie/code/scratch/lesson-19-c-kompiled/interpreter' (x86_64)
Process 52530 stopped
* thread #1, queue = 'com.apple.main-thread', stop reason = breakpoint 1.1
    frame #0: 0x00000001000038c1 interpreter`LESSON-19-C.isEven.sc(VarI=0x0000000101800088) at lesson-19-c.k:6:18
   3   	  imports BOOL
   4   	
   5   	  syntax Bool ::= isEven(Int) [function]
-> 6   	  rule [isEven]: isEven(I) => true requires I %Int 2 ==Int 0
   7   	  rule [isOdd]: isEven(I) => false requires I %Int 2 =/=Int 0
   8   	
   9   	endmodule
(lldb) finish
Process 52649 stopped
* thread #1, queue = 'com.apple.main-thread', stop reason = step out
Return value: (bool) $0 = true

    frame #0: 0x00000001000069e5 interpreter`LblisEven'LParUndsRParUnds'LESSON-19-C'Unds'Bool'Unds'Int(_1=0x0000000101800088) at lesson-19-c.k:5:19
   2   	  imports INT
   3   	  imports BOOL
   4   	
-> 5   	  syntax Bool ::= isEven(Int) [function]
   6   	  rule [isEven]: isEven(I) => true requires I %Int 2 ==Int 0
   7   	  rule [isOdd]: isEven(I) => false requires I %Int 2 =/=Int 0
   8
(lldb)
```

Here we have used the built-in command `finish` to tell us whether the side
condition returned true or not. Note that once again, we see the substitution
that was matched from the left-hand side. Like before, a variable will only
appear here if it is used in the side condition.

## Debugging rule matching

Sometimes it is useful to try to determine why a particular rule did or did
not apply. K provides some basic debugging commands which make it easier
to determine this.

Consider the following K definition (`lesson-19-d.k`):

```k
module LESSON-19-D

  syntax Foo ::= foo(Bar)
  syntax Bar ::= bar(Baz) | bar2(Baz)
  syntax Baz ::= baz() | baz2()

  rule [baz]: foo(bar(baz())) => .K

endmodule
```

Suppose we try to run the program `foo(bar(baz2()))`. It is obvious from this
example why the rule in this definition will not apply. However, in practice,
such cases are not always obvious. You might look at a rule and not immediately
spot why it didn't apply on a particular term. For this reason, it can be
useful to get the debugger to provide a log about how it tried to match that
term. You can do this with the `k match` command. If you are stopped after
having run `k start` or `k step`, you can obtain this log for any rule after
any step by running the command `k match MODULE.label subject` for a particular
top-level rule label.

For example, with the `baz` rule above, we get the following output:

```
(gdb) k match LESSON-19-D.baz subject
Subject:
baz2 ( )
does not match pattern:
baz ( )
```

```
(lldb) k match LESSON-19-D.baz subject
Subject:
baz2 ( )
does not match pattern:
baz ( )
```

As we can see, it provided the exact subterm which did not match against the
rule, as well as the particular subpattern it ought to have matched against.

This command does not actually take any rewrite steps. In the event that
matching actually succeeds, you will still need to run the `k step` command
to advance to the next step.

## Final notes

In addition to the functionality provided above, you have the full power of
GDB or LLDB at your disposal when debugging. Some features are not particularly
well-adapted to K code and may require more advanced knowledge of the
term representation or implementation to use effectively, but anything that
can be done in GDB or LLDB can in theory be done using this debugging functionality.
We suggest you refer to the
[GDB Documentation](https://www.gnu.org/software/gdb/documentation/) or
[LLDB Tutorial](https://lldb.llvm.org/use/tutorial.html) if you
want to try to do something and are unsure as to how.

## Exercises

1. Compile your solution to Lesson 1.18, Exercise 2 with debugging support
enabled and step through several programs you have previously used to test.
Then set a breakpoint on the `isKResult` function and observe the state of the
interpreter when stopped at that breakpoint. Set a breakpoint on the rule for
addition and run a program that causes it to be stopped at that breakpoint.
Finally, step through the program until the addition symbol is at the top
of the K cell, and then use the `k match` command to report the reason why
the subtraction rule does not apply. You may need to modify the definition
to insert some rule labels.

## Next lesson

Once you have completed the above exercises, you can continue to
[Lesson 1.20: K Backends and the Haskell Backend](../20_backends/README.md).
