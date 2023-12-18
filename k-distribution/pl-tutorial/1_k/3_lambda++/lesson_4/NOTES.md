---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

With the current version of the tool (as of Sept 12, 2013), the
callcc-env1.lambda program actually evaluates to 4, as expected.
But the comments in the README are still valid, because it could just as
well evaluate to 3.  For example, just replace ...+x with x+..., and it
should evaluate to 3 now.

Also, the first "fix" suggested in the READMEm to make "+" seqstrict, only
works for that particular program.  It does not fix the problem if we change
the program as indicated above.  In that case "+" it would need to be
seqstrict(2,1).

Also, callcc-env2.lambda evaluates to 3 instead of 4, because of the
particular order in which the strictness of the application operation is
applied.  If you make application seqstrict(2,1) then you get 4.

Dec 06, 2014: Looks like we should discuss the --search and --transition
options before this lesson, and then kompile the definition with option
--transition = computational and krun it with --search.

The README.md says "One is to make `+` `seqstrict` in the semantics, to
enforce its evaluation from left-to-right.  Do it and then run the program
above again;".  Then it continues and says "The problem is now the
non-deterministic evaluation strategy of the function application construct".
Grigore will add this as an exercise, asking reader to fix this
non-determinism. Then ask them to propose another example where you still get
non-determinism; can they?
