---
copyright: Copyright (c) Runtime Verification, Inc. All Rights Reserved.
---

Syntax of JSON
==============

K provides builtin support for reading/writing to JSON. While the `JSON-SYNTAX`
module is not precisely the syntax of JSON (utilizing K's syntax for strings,
integers, and floating point numbers rather than the syntax used by JSON),
you can still convert directly to/from the actual syntax of JSON using
the `JSON2String` and `String2JSON` hooks.

```k
module JSON-SYNTAX
    imports INT-SYNTAX
    imports STRING-SYNTAX
    imports BOOL-SYNTAX
    imports FLOAT-SYNTAX

    syntax JSONs   ::= List{JSON,","}      [symbol(JSONs)]
    syntax JSONKey ::= String
    syntax JSON    ::= "null"              [symbol(JSONnull)]
                     | String | Int | Float | Bool
                     | JSONKey ":" JSON    [symbol(JSONEntry)]
                     | "{" JSONs "}"       [symbol(JSONObject)]
                     | "[" JSONs "]"       [symbol(JSONList)]
endmodule
```

Conversion between `JSON` and `String`
--------------------------------------

Given a string written in valid JSON, you can convert it to the `JSON`
sort with the `String2JSON` function. Assuming the user has not extended
the syntax of the `JSON` sort with their own constructors, any term of sort
`JSON` can also be converted to a `String` using the `JSON2String` function.

```k
module JSON
    imports JSON-SYNTAX

    syntax String ::= JSON2String(JSON) [function, symbol(JSON2String), hook(JSON.json2string)]

    syntax JSON ::= String2JSON(String) [function, symbol(String2JSON), hook(JSON.string2json)]
endmodule
```
