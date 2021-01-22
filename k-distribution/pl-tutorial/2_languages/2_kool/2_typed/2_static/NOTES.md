<!-- Copyright (c) 2016-2019 K Team. All Rights Reserved. -->

Why is the following happening at line 347?  It should infer the sort Stmts for S:

  rule <task> <k> {S} => block ...</k> <tenv> Rho </tenv> R </task>
       (.Bag => <task> <k> S </k> <tenv> Rho </tenv> R </task>)

  [Error] Critical: Could not infer a sort for variable 'S' to match every location.

Similarly at line 517.

