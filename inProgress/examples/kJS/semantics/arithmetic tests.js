function arithTest(base) {
	function add(a, b) {return a + b;}
	function sub(a, b) {return a - b;}
	function mul(a, b) {return a * b;}
	function div(a, b) {return a / b;}
	function mod(a, b) {return a % b;}
	function rdiv(a, b) {return b / a;}
	function rmod(a, b) {return b % a;}
	
	var ops = [add, sub, mul, div, mod, rdiv, rmod],
		opNames = ["+", "-", "*", "/", "%", "/", "%"],
		opDirection = [1, 1, 1, 1, 1, -1, -1],
		values = [0, 11, -2.2, "33", "", NaN, Infinity, {}, null, undefined],
		results = {};
	
	values.forEach(function (value) {
		ops.forEach(function (op, index) {
			var direction = opDirection[index],
				a = direction > 0 ? base : value,
				b = direction > 0 ? value : base,
				tag = a + " " + opNames[index] + " " + b;
			results[tag] = op.call(null, a, b);
		});
	});
	return results;
}

