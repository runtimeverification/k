<!-- Copyright (c) 2016-2019 K Team. All Rights Reserved. -->

Add an exercise somewhere with a print which first evaluates all its arguments
and THEN prints them.  The idea is to define `print` to be `strict` and to
make the `AExps` list construct `seqstrict`, so lists of arithmetic
expressions get evaluated from left-to-right whenever they reach the top of
the `<k/>` cell (replace `seqstrict` with `strict` if you want expressions in
a list to evaluate non-deterministically and interleaved).
