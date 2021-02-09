<!-- Copyright (c) 2016-2019 K Team. All Rights Reserved. -->

This is not well tested now, and it was not well tested in v3.6 either.
We should add some rules as transitions, too, and then use search on all
the examples.

Exercises not revised yet.

.Bag should be . throughout this definition #1772

There seems to be a problem with defining auxiliary constructs of sort
KItem when we want to use them as a particular sort in rule.  We had to
declare them as construct for that sort instead.  May want to explain
this a bit in the Latex discussion (related to #1803):
+  syntax Exp ::= lookup(Int)
-  syntax KItem ::= lookup(Int)

We currently add Vals to KResult, but we should have a better pattern for
List{Sort} and in general for any collections, where we make them hybrid
(they become KResults when their elements become KResults)
