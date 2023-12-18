---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

* Cut-and-paste is a poor-man's approach to reuse.

Indeed, it is.  A better way to reuse, which requires a bit of planning ahead,
is to put each feature in its own module.  Then you can simply include the
modules containing the features you want to reuse.  Our point in this lesson
was that such reuse is possible, not to teach the best way to do it in
practice.  Good methodologies on how to use a technology are equally important.

* Do we need an env/store split?  Couldn't we just work with a state?

Since in our language so far we never change the value of a variable, it
happens to be OK to only keep a state.  That is, to collapse env/store into
state, then embed the state in closures and restore the state instead of the
environment.  However, this simplistic approach breaks as soon as we add
references to our language, because functions can then modify the environment
in which they were declared, so we would have to carry over those changes when
returning from function invocations, which would be quite difficult.
