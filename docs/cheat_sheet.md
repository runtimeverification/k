K Cheat Sheet
=============

This is a quick reference of the most commonly used K tools.

```
kompile (--gen-bison-parser)? {file}                : generate parser, optionally with ahead of time
krun {file}                                         : interpret file
krun -cPGM='{string}'                               : interpret string
kast --output (kore | kast) (-e|{file})             : parse expression or file
kompile (--enable-search --backend haskell)? {file} : generate parser, enabling non-deterministic run
krun (--search-all)? {file}                         : interpret file, evaluating non-deterministic runs as well
foo-kompiled/parser_PGM {file}                      : ahead of time parse
kompile (--main-module)? (--syntax-module)? {file}  : generate parser for {file}.k {file}-syntax.k, explicitly state main modules
kparse <file> | kore-print -                        : parse and unparse a file
kompile {file} -ccopt -g -ccopt -O1                 : generate debuggable output for {file}.k
krun {file} --debugger                              : debug K code
kprove {file}                                       : Verify specs in {file}
```

Durring GDB debugging session:

```
break {file}:{linenum}                              : add a breakpoint to {file}'s {linenum} numbered line
k match {module}.{label} subject                    : investigate matching
```
