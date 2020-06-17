// Copyright (c) 2020 K Team. All Rights Reserved.

module JSON-SYNTAX
    imports INT-SYNTAX
    imports STRING-SYNTAX
    imports BOOL-SYNTAX
    imports FLOAT-SYNTAX

    syntax JSONs   ::= List{JSON,","}      [klabel(JSONs)      , symbol]
    syntax JSONKey ::= String
    syntax JSON    ::= "null"              [klabel(JSONnull)   , symbol]
                     | String | Int | Float | Bool
                     | JSONKey ":" JSON    [klabel(JSONEntry)  , symbol]
                     | "{" JSONs "}"       [klabel(JSONObject) , symbol]
                     | "[" JSONs "]"       [klabel(JSONList)   , symbol]
endmodule

module JSON
    imports JSON-SYNTAX

    syntax String ::= JSON2String(JSON) [function, hook(JSON.json2string)]

    syntax JSON ::= String2JSON(String) [function, hook(JSON.string2json)]
endmodule
