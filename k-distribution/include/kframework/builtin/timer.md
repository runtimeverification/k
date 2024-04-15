---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

```k
module TIMER-SYNTAX
    imports INT-SYNTAX
endmodule

module TIMER
    imports TIMER-SYNTAX

    syntax K ::= "timerStart" "(" ")" [function, hook(TIMER.timerStart)]
    syntax K ::= "timerStart" "(" Int ")" [function, hook(TIMER.timerStartArg)]

    syntax K ::= "timerStop" "(" ")" [function, hook(TIMER.timerStop)]
endmodule
```
