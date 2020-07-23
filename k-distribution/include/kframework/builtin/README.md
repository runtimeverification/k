---
copyright: Copyright (c) 2020 K Team. All Rights Reserved.
---

K Builtins
==========

The K Builtins (also referred to as the K Prelude or the K Standard Library)
consists of several files which contain definitions that make working with K
simpler.

-   [domains](domains.k): Basic datatypes which are universally useful.
-   [kast](kast.k): Representation of K internal data-structures (not to be
    included in normal definitions).
-   [prelude](prelude.k): Legacy file which includes domains.k and kast.k.
-   [ffi](ffi.md): FFI interface for calling out to native C code from K.
-   [json](json.md): JSON datatype and parsers/unparsers for JSON strings.
-   [rat](rat.md): Rational number representation.
-   [substitution](substitution.k): Hooked implementation of capture-aware
    sustitution for K definitions.
-   [unification](unification.k): Hooked implementation of unification
    exposed directly to K definitions.
