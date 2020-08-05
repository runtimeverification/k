---
copyright: Copyright (c) 2015-2020 K Team. All Rights Reserved.
---

K Prelude
=========

The following files, integral to defining semantics in K, are automatically
required by every definition via this file. This behavior can be disabled
via `kompile --no-prelude`, however, semantics will likely break unless
they provide their own versions of these files, which are assumed to exist
by the compiler. There are, however, circumstances where passing this flag is
appropriate, such as if you are manually requiring these files in your
definition, if your definition was automatically condensed into a single file
with `kompile -E`, or if you wish to modify the inner syntax of K by providing
your own version of these files with different syntax.

```k
require "kast.k"
require "domains.md"
```
