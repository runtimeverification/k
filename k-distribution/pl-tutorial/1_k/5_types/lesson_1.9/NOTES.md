---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

This currently does NOT work, because of the rules

    rule _:Int => int                            [anywhere]
    rule _:Bool => bool                          [anywhere]

which now rewrite ANY integer ANYWHERE to "int", including integers
that appear in the internal data-structures/functions of the builtins.
We will need to allow a strategy where "anywhere" means anywhere in one
or more computational cells.
