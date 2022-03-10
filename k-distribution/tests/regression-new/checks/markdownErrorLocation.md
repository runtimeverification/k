1
 ```k
 // keep indentation
 module MARKDOWNERRORLOCATION-SYNTAX
 endmodule
 ```
7
```{.a .b}
9
```
11
```{.k .x}
module MARKDOWNERRORLOCATION
  imports INT
```

``` { not used
}
```

 ```k
  rule 21 // pandoc would think this is line 20, column 7
 ```

```{.y .k}
endmodule // pandoc would miss this last unfinished block

