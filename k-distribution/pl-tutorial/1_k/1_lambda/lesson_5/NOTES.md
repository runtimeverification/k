<!-- Copyright (c) 2016-2019 K Team. All Rights Reserved. -->

The builtins have changed, they are now generic for all backends.

Talk about sort inference for variables, for example from `I1 +Int I2`
we infer the sort of `I1` and `I2` is `Int`.

Check the entire tutorial for instances where we give the sort of a
variable but we don't have to.  Many of those are artifacts since we were
not able to infer sorts that well.
