Riot.run(function() {
	given("an AST to S-Expression converter", function () {
		var empty = [], s_exp;	
		should("handle empty array", empty.asSExpression()).equals("()");
		
		var single = ["one item"];
		should("handle array with single element", single.asSExpression()).equals("(\"one item\")");
		
		var several = ["one","plus","two","=",3];
		should("handle single level array", several.asSExpression()).equals(
			"(\"one\", \"plus\", \"two\", \"=\", 3)"
		);
		
		var nested = 
			["none",[],["uno"],["singles", 2, 3],["deep",["deeper",4,5,["deepest", "a", "b"]]]];
		should("handle single multi-level nested array", nested.asSExpression()).equals(
			"(\"none\", (), (\"uno\"), (\"singles\", 2, 3), " +
			  "(\"deep\", (\"deeper\", 4, 5, (\"deepest\", \"a\", \"b\"))))"
		);
		
		var Token = function Token(str) {this.name = str;};
		Token.prototype.toString = function() { return this.name; };
		
		var token = new Token("block");
			terminals = [123, 0, -123, true, false, null, undefined, "str", token, []];
		should("handle terminals", terminals.asSExpression()).equals(
			"(123, 0, -123, true, false, null, undefined, \"str\", $block, ())"
		);

		var strings = ["str", "str w spaces", "str w \"quotes\" inside"];
		should("handle strings", strings.asSExpression()).equals(
			"(\"str\", \"str w spaces\", \"str w \\\"quotes\\\" inside\")"
		);

	});
	
	given("an AST diagram printer", function () {
		var empty = [];
		should("handle []", empty.asDiagram()).equals(
'"         \\' + '\n' +
' ---()    \\' + '\n' +
'          \\"'
		);

		var simplest = ["a"];	
		should("handle [a]", simplest.asDiagram()).equals(
'"                \\' + '\n' +
' ---()--> "a"    \\' + '\n' +
'                 \\"'
		);

		var simple = ["a", "b", "c"];
		should("handle [a, b, c]", simple.asDiagram()).equals(
'"                \\' + '\n' +
' ---(---> "a"    \\' + '\n' +
'    |---> "b"    \\' + '\n' +
'    )---> "c"    \\' + '\n' +
'                 \\"'
		);

		var simplestNestedOnce = [["a"]];
		should("handle [[a]]", simplestNestedOnce.asDiagram()).equals(
'"                    \\' + '\n' +
' ---()--()--> "a"    \\' + '\n' +
'                     \\"'
		);
		
		var simpleNestedOnce = [["a", "b", "c"]];
		should("handle [[a, b, c]]", simpleNestedOnce.asDiagram()).equals(
'"                    \\' + '\n' +
' ---()--(---> "a"    \\' + '\n' +
'        |---> "b"    \\' + '\n' +
'        )---> "c"    \\' + '\n' +
'                     \\"'
		);

		var multiNested = ["a", [["b", "c"], "d"]];
		should("handle [a, [[b, c], d]]", multiNested.asDiagram()).equals(
'"                        \\' + '\n' +
' ---(---> "a"            \\' + '\n' +
'    )---(---(---> "b"    \\' + '\n' +
'        |   )---> "c"    \\' + '\n' +
'        )---> "d"        \\' + '\n' +
'                         \\"'
		);

		var moreMultiNested = ["a", ["b", "c", ["d"]], "e", ["f"]];
		should("handle [a, [b, c, [d]], e, [f]]", moreMultiNested.asDiagram()).equals(
'"                        \\' + '\n' +
' ---(---> "a"            \\' + '\n' +
'    |---(---> "b"        \\' + '\n' +
'    |   |---> "c"        \\' + '\n' +
'    |   )---()--> "d"    \\' + '\n' +
'    |---> "e"            \\' + '\n' +
'    )---()--> "f"        \\' + '\n' +
'                         \\"'
		);	

		var longNested = 
			["a", ["b", "c", ["d", "e", "f"], ["g"], [["h"]]], [["i"], ["j"]], ["k", "l", "m"]];

		should("handle [a, [b, c, [d, e, f], [g], [[h]]], [[i], [j]], [k, l, m]]", 
			longNested.asDiagram()).equals(
'"                            \\' + '\n' +
' ---(---> "a"                \\' + '\n' +
'    |---(---> "b"            \\' + '\n' +
'    |   |---> "c"            \\' + '\n' +
'    |   |---(---> "d"        \\' + '\n' +
'    |   |   |---> "e"        \\' + '\n' +
'    |   |   )---> "f"        \\' + '\n' +
'    |   |---()--> "g"        \\' + '\n' +
'    |   )---()--()--> "h"    \\' + '\n' +
'    |---(---()--> "i"        \\' + '\n' +
'    |   )---()--> "j"        \\' + '\n' +
'    )---(---> "k"            \\' + '\n' +
'        |---> "l"            \\' + '\n' +
'        )---> "m"            \\' + '\n' +
'                             \\"'
		);

		var source = "                                  \
		    var count = elements.length;                \
		    var index, element, separator;              \
		    var accumulator = accumulator__ || [];      \
		separator_ = separator_ || ',';                 \
		";
		
		var ast = parse(source, false, true);
		
		should("handle short source string", ast.asDiagram()).equals(
'"                                                    \\' + '\n' +
' ---(---> "toplevel"                                 \\' + '\n' +
'    )---(---(---> $var                               \\' + '\n' +
'        |   )---()--(---> "count"                    \\' + '\n' +
'        |           )---(---> "dot"                  \\' + '\n' +
'        |               |---(---> "name"             \\' + '\n' +
'        |               |   )---> "elements"         \\' + '\n' +
'        |               )---> "length"               \\' + '\n' +
'        |---(---> $var                               \\' + '\n' +
'        |   )---(---()--> "index"                    \\' + '\n' +
'        |       |---()--> "element"                  \\' + '\n' +
'        |       )---()--> "separator"                \\' + '\n' +
'        |---(---> $var                               \\' + '\n' +
'        |   )---()--(---> "accumulator"              \\' + '\n' +
'        |           )---(---> "binary"               \\' + '\n' +
'        |               |---> "||"                   \\' + '\n' +
'        |               |---(---> "name"             \\' + '\n' +
'        |               |   )---> "accumulator__"    \\' + '\n' +
'        |               )---(---> "array"            \\' + '\n' +
'        |                   )---()                   \\' + '\n' +
'        )---(---> $stat                              \\' + '\n' +
'            )---(---> "assign"                       \\' + '\n' +
'                |---> true                           \\' + '\n' +
'                |---(---> "name"                     \\' + '\n' +
'                |   )---> "separator_"               \\' + '\n' +
'                )---(---> "binary"                   \\' + '\n' +
'                    |---> "||"                       \\' + '\n' +
'                    |---(---> "name"                 \\' + '\n' +
'                    |   )---> "separator_"           \\' + '\n' +
'                    )---(---> "string"               \\' + '\n' +
'                        )---> ","                    \\' + '\n' +
'                                                     \\"'
		);
	});
});
