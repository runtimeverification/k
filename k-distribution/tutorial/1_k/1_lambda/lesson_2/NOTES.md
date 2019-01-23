<!-- Copyright (c) 2016-2019 K Team. All Rights Reserved. -->

Substitution has been reimplemented in the meanwhile, where the fresh
variables are resolved locally.  So there is no global counter for
fresh variables anymore as shown in the video, and fewer variable
renamings take place.

When calling krun on the programs in lesson_1, a different path is
shown than in the README.md.

Marking the beta-reduction rule with `[anywhere]` will give us the
conventional lambda-calculus.  A new lesson has been added, 2.5,
showing that.  The README.md file should be changed at the end to
point to lesson 2.5.
