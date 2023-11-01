---
copyright: Copyright (c) K Team. All Rights Reserved.
---

K Builtins
==========

The K Builtins (also referred to as the K Prelude or the K Standard Library)
consists of several files which contain definitions that make working with K
simpler. These files can be found under `include/kframework/builtin` in your K
installation directory, and can be imported with `requires "FILENAME"` (without
the path prefix).

-   [domains](builtin/domains.md): Basic datatypes which are universally useful.
-   [kast](builtin/kast.md): Representation of K internal data-structures (not to be
    included in normal definitions).
-   [prelude](builtin/prelude.md): Automatically included into every K definition.
-   [ffi](builtin/ffi.md): FFI interface for calling out to native C code from K.
-   [json](builtin/json.md): JSON datatype and parsers/unparsers for JSON strings.
-   [rat](builtin/rat.md): Rational number representation.
-   [substitution](builtin/substitution.md): Hooked implementation of capture-aware
    sustitution for K definitions.
-   [unification](https://github.com/runtimeverification/k/blob/master/k-distribution/include/kframework/builtin/unification.k): Hooked implementation of unification
    exposed directly to K definitions.
