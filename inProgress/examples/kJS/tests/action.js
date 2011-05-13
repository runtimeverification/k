var source = "									\
	var count = elements.length;				\
	var index, element;							\
	var accumulator = accumulator__ || [];		\
	separator_ = separator_ || ',';				\
";

var answer = parse(source, false, true);
var sexp = answer.asSExpression();
alert(answer);
