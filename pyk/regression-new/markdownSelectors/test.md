---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

Test
====
```k
module TEST-SYNTAX
  imports INT
endmodule
module TEST
  imports INT
```

```{.k}
  configuration <k> $PGM:K </k> <r> 0 </r>
```

```{.discard}
  rule <r> 0 => 1 </r>
```

```{.keep}
  rule <k> 0 => 1 </k>
```

```{.k .keep}
  rule <k> 1 => 2 </k>
```

```{.k .discard .numberLines startFrom="0"}
  rule <k> 2 => 3 </k>
```

```{.keep .discard}
  rule <r> 0 => 1 </r>
```

```k
endmodule
```
