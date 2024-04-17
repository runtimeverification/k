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
    syntax K ::= "timerStop" "(" ")" [function, hook(TIMER.timerStop)]
    syntax K ::= "timerCount" "(" Int ")" [function, hook(TIMER.timer)]
    
endmodule
```
