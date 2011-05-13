
var source = '                                                                                 \
Array.prototype.asSExpression = function asSExpression(options_, accumulatedSubstrings__) {    \
    "use strict";                                                                              \
    var element,                                                                               \
        index = 0,                                                                             \
        count = this.length,                                                                   \
        substrings = accumulatedSubstrings__ || [],                                            \
        options = options_ || {},                                                              \
        separator =  options.separator || ", ";                                                \
                                                                                               \
    substrings.push( "(" );                                                                    \
    if (count > 0) {                                                                           \
        do {                                                                                   \
            element = this[index];                                                             \
            if (Array.isArray(element)) {                                                      \
                element.asSExpression(options, substrings);                                    \
            } else {                                                                           \
                substrings.push(element.toString());                                           \
            }                                                                                  \
            index += 1;                                                                        \
            if (index >= count) {break;}                                                       \
            substrings.push(separator);                                                        \
        } while (true);                                                                        \
    }                                                                                          \
    substrings.push( ")" );                                                                    \
    if (accumulatedSubstrings__ === undefined) {return substrings.join("");}                   \
};                                                                                             \
';

var source1 = '                                    \
	var a = [true, false, null, undefined, "a b"]; \
	var l = a.length;                              \
';

var ast1 = parse(source1, false, true);

var source2 = '                \
	var a = 1, b = 2, c;          \
	if (a < b) {c = "a b";} \
';
var ast2 = parse(source2, false, true);


var ast = parse(source, false, true);
var str = ast.generate();

var sexp = ast.asSExpression();
sexp = sexp;

// alert(str);