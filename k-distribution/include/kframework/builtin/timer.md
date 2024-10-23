---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

```k
module TIMER
    syntax K ::= "timerStart" "(" ")" [function, hook(TIMER.timerStart)]

    syntax K ::= "timerStop" "(" ")" [function, hook(TIMER.timerStop)]
endmodule
```
